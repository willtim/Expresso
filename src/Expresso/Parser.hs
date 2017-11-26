{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Expresso.Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Data.Maybe
import Text.Parsec hiding (many, optional, parse, (<|>))
import Text.Parsec.Language (emptyDef)
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as P
import qualified Text.Parsec.Token as P

import Expresso.Syntax
import Expresso.Type
import Expresso.Utils

------------------------------------------------------------
-- Resolve imports

resolveImports :: ExpI -> ExceptT String IO Exp
resolveImports = cataM alg where
  alg (InR (K (Import path)) :*: _) = do
      res <- ExceptT $ readFile path >>= return . parse path
      resolveImports res
  alg (InL e :*: pos) = return $ Fix (e :*: pos)

------------------------------------------------------------
-- Parser

parse :: SourceName -> String -> Either String ExpI
parse src = showError . P.parse (whiteSpace *> pExp <* P.eof) src

pExp     = pImport
        <|> pLam
        <|> pLet
        <|> pCond
        <|> pCase
        <|> pOpExp
        <?> "expression"

pImport  = mkImport
        <$> getPosition
        <*> (reserved "import" *> stringLiteral)
        <?> "import"

pLet     = reserved "let" *>
           (flip (foldr mkLet) <$> (semiSep1 ((,) <$> getPosition <*> pLetDecl))
                               <*> (reserved "in" *> pExp))
           <?> "let expression"

pLetDecl = (,) <$> pLetBind
               <*> (reservedOp "=" *> pExp <* whiteSpace)

pLam     = mkLam
        <$> getPosition
        <*> try (pBind <* reservedOp ":" <* whiteSpace)
        <*> pExp
        <?> "lambda expression"

pAtom    = pPrim <|> try pVar <|> parens pExp

pVar     = mkVar <$> getPosition <*> identifier

pPrim    = pNumber           <|>
           pBool             <|>
           pChar             <|>
           pMaybe            <|>
           pDifferenceRecord <|>
           pRecord           <|>
           pVariant          <|>
           pVariantEmbed     <|>
           pList             <|>
           pString           <|>
           pPrimFun

pCond    = (\pos -> mkTertiaryOp pos Cond)
               <$> getPosition
               <*> (reserved "if"   *> pExp)
               <*> (reserved "then" *> pExp)
               <*> (reserved "else" *> pExp)
               <?> "if expression"

pOpExp   = P.buildExpressionParser opTable pApp

-- NB: assumes "-1" and "+1" are not valid terms
pApp     = mkApp <$> getPosition <*> pTerm <*> many pTerm

pTerm    = mkRecordRestrict
        <$> getPosition
        <*> ((\pos -> foldl (mkRecordSelect pos))
            <$> getPosition
            <*> pAtom
            <*> try (many pSelect))
        <*> optional (reservedOp "\\" *> identifier)

opTable  = [ [ prefix "-" Neg
             ]
           , [ binary ">>" FwdComp        P.AssocRight
             , binary "<<" BwdComp        P.AssocRight
             ]
           , [ binary "*" (ArithPrim Mul) P.AssocLeft
             , binary "/" (ArithPrim Div) P.AssocLeft
             ]
           , [ binary "+" (ArithPrim Add) P.AssocLeft
             , binary "-" (ArithPrim Sub) P.AssocLeft
             ]
           , [ binary "++" ListAppend     P.AssocLeft
             , binary "::" ListCons       P.AssocRight
             ]
           , [ binary "==" Eq             P.AssocLeft
             , binary "/=" NEq            P.AssocLeft
             , binary ">"  (RelPrim RGT)  P.AssocLeft
             , binary ">=" (RelPrim RGTE) P.AssocLeft
             , binary "<"  (RelPrim RLT)  P.AssocLeft
             , binary "<=" (RelPrim RLTE) P.AssocLeft
             ]
           , [ binary "&&" And            P.AssocRight
             ]
           , [ binary "||" Or             P.AssocRight
             ]
           ]

pPrimFun = msum
  [ fun "error"   ErrorPrim
  , fun "show"    Show
  , fun "not"     Not
  , fun "maybe"   MaybePrim
  , fun "foldr"   ListFoldr
  , fun "null"    ListNull
  , fun "fix"     FixPrim
  , fun "double"  Double
  , fun "floor"   Floor
  , fun "ceiling" Ceiling
  , fun "abs"     Abs
  , fun "mod"     Mod
  ]
  where
    fun sym prim = reserved sym *> ((\pos -> mkPrim pos prim) <$> getPosition)

binary sym prim =
    P.Infix $ reservedOp sym *> ((\pos -> mkBinOp pos prim) <$> getPosition)
prefix sym prim =
    P.Prefix $ reservedOp sym *> ((\pos -> mkUnaryOp pos prim) <$> getPosition)

pSelect = reservedOp "." *> identifier

pNumber = (\pos -> either (mkInteger pos) (mkDouble pos))
       <$> getPosition
       <*> naturalOrFloat

pBool = (\pos -> mkPrim pos . Bool)
     <$> getPosition
     <*> (reserved "True"  *> pure True <|>
          reserved "False" *> pure False)

pChar = (\pos -> mkPrim pos . Char)
     <$> getPosition
     <*> charLiteral

pString = (\pos -> mkPrim pos . String)
       <$> getPosition
       <*> stringLiteral

pBind = Arg <$> identifier
    <|> RecArg <$> pFieldPuns

pLetBind = try (RecWildcard <$ reservedOp "{..}") <|> pBind

pFieldPuns = braces $ identifier `sepBy` comma

data Entry = Extend Label ExpI | Update Label ExpI

pRecord = (\pos -> fromMaybe (mkRecordEmpty pos))
       <$> getPosition
       <*> (braces $ optionMaybe pRecordBody)

pRecordBody = mkRecordExtend <$> getPosition <*> pRecordEntry <*> pRest
  where
    pRest = (comma          *> pRecordBody)  <|>
            (reservedOp "|" *> pExp)         <|>
            (mkRecordEmpty <$> getPosition)

pDifferenceRecord = mkDifferenceRecord
    <$> getPosition
    <*> (try (reservedOp "{|") *> (pRecordEntry `sepBy1` comma)
           <* reservedOp "|}")

mkDifferenceRecord :: Pos -> [Entry] -> ExpI
mkDifferenceRecord pos entries =
    withPos pos $ ELam (Arg "#r") $
        foldr (mkRecordExtend pos) (withPos pos $ EVar "#r") entries

pRecordEntry =
    try (Extend <$> identifier <*> (reservedOp "=" *> pExp))  <|>
    try (Update <$> identifier <*> (reservedOp ":=" *> pExp)) <|>
    mkFieldPun <$> getPosition <*> identifier

pVariant = mkVariant <$> getPosition <*> pVariantLabel

pVariantEmbed = mkVariantEmbed
             <$> getPosition
             <*> (try (reservedOp "<|") *> (pEmbedEntry `sepBy1` comma)
                    <* reservedOp "|>")
             <?> "variant embed expression"
    where
      pEmbedEntry = (,) <$> getPosition <*> pVariantLabel

pCase = mkCase <$> getPosition
               <*> (reserved "case" *> pApp <* reserved "of")
               <*> (braces pCaseBody)
               <?> "case expression"

pCaseBody = mkCaseAlt <$> getPosition <*> pCaseAlt <*> pRest
  where
    pRest = (comma          *> pCaseBody)   <|>
            (reservedOp "|" *> pLam)        <|>
            (\pos -> mkPrim pos EmptyAlt) <$> getPosition

pCaseAlt =
    (try (Extend <$> pVariantLabel
                 <*> (whiteSpace *> pLam)) <|>
     try (Update <$> (reserved "override" *> pVariantLabel)
                 <*> (whiteSpace *> pLam)))
    <?> "case alternative"

pVariantLabel = (:) <$> upper <*> identifier

pMaybe =  (\pos -> mkPrim pos JustPrim)    <$> getPosition <* reserved "Just"
      <|> (\pos -> mkPrim pos NothingPrim) <$> getPosition <* reserved "Nothing"

pList = brackets pListBody
  where
    pListBody = (\pos -> foldr mkListCons (mkListEmpty pos))
        <$> getPosition
        <*> ((,) <$> getPosition <*> pExp) `sepBy` comma
        <?> "list expression"

mkImport :: Pos -> FilePath -> ExpI
mkImport pos path = withAnn pos $ InR $ K $ Import path

mkInteger :: Pos -> Integer -> ExpI
mkInteger pos = mkPrim pos . Int

mkDouble :: Pos -> Double -> ExpI
mkDouble pos = mkPrim pos . Dbl

mkCase :: Pos -> ExpI -> ExpI -> ExpI
mkCase pos scrutinee caseF = mkApp pos caseF [scrutinee]

mkCaseAlt :: Pos -> Entry -> ExpI -> ExpI
mkCaseAlt pos (Extend l altLamE) contE =
    mkApp pos (mkPrim pos $ VariantElim l) [altLamE, contE]
mkCaseAlt pos (Update l altLamE) contE =
    mkApp pos (mkPrim pos $ VariantElim l)
          [ altLamE
          , mkLam pos (Arg "#r")
                      (mkApp pos contE [mkEmbed $ withPos pos $ EVar "#r"])
          ]
  where
    mkEmbed e = mkApp pos (mkPrim pos $ VariantEmbed l) [e]

mkVariant :: Pos -> Label -> ExpI
mkVariant pos l = mkPrim pos $ VarianttoValueect l

mkVariantEmbed :: Pos -> [(Pos , Label)] -> ExpI
mkVariantEmbed pos ls =
    withPos pos $ ELam (Arg "#r") $
        foldr f (withPos pos $ EVar "#r") ls
  where
    f (pos, l) k = mkApp pos (mkPrim pos $ VariantEmbed l) [k]

mkLam :: Pos -> Bind Name -> ExpI -> ExpI
mkLam pos b e = withPos pos (ELam b e)

mkVar :: Pos -> Name -> ExpI
mkVar pos name = withPos pos (EVar name)

mkLet :: (Pos, (Bind Name, ExpI)) -> ExpI -> ExpI
mkLet (pos, (b, e1)) e2 = withPos pos (ELet b e1 e2)

mkTertiaryOp :: Pos -> Prim -> ExpI -> ExpI -> ExpI -> ExpI
mkTertiaryOp pos p x y z = mkApp pos (mkPrim pos p) [x, y, z]

mkBinOp :: Pos -> Prim -> ExpI -> ExpI -> ExpI
mkBinOp pos p x y = mkApp pos (mkPrim pos p) [x, y]

mkUnaryOp  :: Pos -> Prim -> ExpI -> ExpI
mkUnaryOp pos p x = mkApp pos (mkPrim pos p) [x]

mkRecordSelect :: Pos -> ExpI -> Label -> ExpI
mkRecordSelect pos r l = mkApp pos (mkPrim pos $ RecordSelect l) [r]

mkRecordExtend :: Pos -> Entry -> ExpI -> ExpI
mkRecordExtend pos (Extend l e) r =
    mkApp pos (mkPrim pos $ RecordExtend l) [e, r]
mkRecordExtend pos (Update l e) r =
    mkApp pos (mkPrim pos $ RecordExtend l) [e, mkRecordRestrict pos r $ Just l]

mkRecordEmpty :: Pos -> ExpI
mkRecordEmpty pos = mkPrim pos RecordEmpty

mkRecordRestrict :: Pos -> ExpI -> Maybe Label -> ExpI
mkRecordRestrict pos e = maybe e $ \l -> mkApp pos (mkPrim pos $ RecordRestrict l) [e]

mkFieldPun :: Pos -> Label -> Entry
mkFieldPun pos l = Extend l (withPos pos $ EVar l)

mkListCons :: (Pos, ExpI) -> ExpI -> ExpI
mkListCons (pos, x) xs = mkApp pos (mkPrim pos ListCons) [x, xs]

mkListEmpty :: Pos -> ExpI
mkListEmpty pos = mkPrim pos ListEmpty

mkApp :: Pos -> ExpI -> [ExpI] -> ExpI
mkApp pos f = foldl (\g -> withPos pos . EApp g) f

mkPrim :: Pos -> Prim -> ExpI
mkPrim pos p = withPos pos $ EPrim p

withPos :: Pos -> ExpF Name Bind ExpI -> ExpI
withPos pos = withAnn pos . InL

------------------------------------------------------------
-- Language definition for Lexer

languageDef :: P.LanguageDef st
languageDef = emptyDef
    { P.commentStart   = "{-"
    , P.commentEnd     = "-}"
    , P.commentLine    = "--"
    , P.nestedComments = True
    , P.identStart     = letter
    , P.identLetter    = alphaNum <|> oneOf "_'"
    , P.opStart        = P.opLetter languageDef
    , P.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
    , P.reservedOpNames= [ "=", ":", "-", "*", "/", "+"
                         , "++", "::", "|", ",", ".", "\\"
                         , "{|", "|}", ":=", "{..}"
                         , "==", "/=", ">", ">=", "<", "<="
                         , "&&", "||"
                         ]
    , P.reservedNames  = [ "let", "in", "if", "then", "else", "case", "of"
                         , "True", "False", "Just", "Nothing"
                         ]
    , P.caseSensitive  = True
    }


------------------------------------------------------------
-- Lexer

lexer = P.makeTokenParser languageDef

identifier = P.identifier lexer
reserved = P.reserved lexer
operator = P.operator lexer
reservedOp = P.reservedOp lexer
charLiteral = P.charLiteral lexer
stringLiteral = P.stringLiteral lexer
--natural = P.natural lexer
--integer = P.integer lexer
--float = P.float lexer
naturalOrFloat = P.naturalOrFloat lexer
--decimal = P.decimal lexer
--hexadecimal = P.hexadecimal lexer
--octal = P.octal lexer
symbol = P.symbol lexer
lexeme = P.lexeme lexer
whiteSpace = P.whiteSpace lexer
parens = P.parens lexer
braces = P.braces lexer
angles = P.angles lexer
brackets = P.brackets lexer
semi = P.semi lexer
comma = P.comma lexer
colon = P.colon lexer
dot = P.dot lexer
semiSep = P.semiSep lexer
semiSep1 = P.semiSep1 lexer
commaSep = P.commaSep lexer
commaSep1 = P.commaSep1 lexer
