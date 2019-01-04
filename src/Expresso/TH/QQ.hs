{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      : Expresso.TH.QQ
-- Copyright   : (c) Tim Williams 2017-2019
-- License     : BSD3
--
-- Maintainer  : info@timphilipwilliams.com
-- Stability   : experimental
-- Portability : portable
--
-- Quasi-quoters for defining Expresso types in Haskell.
--
module Expresso.TH.QQ (expressoType) where

import Control.Exception

import Language.Haskell.TH (ExpQ, Loc(..), Q, location, runIO)
import Language.Haskell.TH.Quote (QuasiQuoter(..), dataToExpQ)

import qualified Text.Parsec as P
import qualified Text.Parsec.Pos as P
import Text.Parsec.String

import Expresso.Parser

-- | Expresso Quasi-Quoter for type declarations.
expressoType :: QuasiQuoter
expressoType = def { quoteExp = genTypeDecl }

def :: QuasiQuoter
def = QuasiQuoter
    { quoteExp  = failure "expressions"
    , quotePat  = failure "patterns"
    , quoteType = failure "types"
    , quoteDec  = failure "declarations"
    }
  where
    failure kind =
        fail $ "This quasi-quoter does not support splicing " ++ kind

genTypeDecl :: String -> ExpQ
genTypeDecl str = do
    l <- location'
    c <- runIO $ parseIO (P.setPosition l *> topLevel pTypeAnn) str
    dataToExpQ (const Nothing) c

-- | find the current location in the Haskell source file and convert it to parsec @SourcePos@.
location' :: Q P.SourcePos
location' = aux <$> location
  where
    aux :: Loc -> P.SourcePos
    aux loc = uncurry (P.newPos (loc_filename loc)) (loc_start loc)

parseIO :: Parser a -> String -> IO a
parseIO p str =
  case P.parse p "" str of
    Left err -> throwIO (userError (show err))
    Right a  -> return a
