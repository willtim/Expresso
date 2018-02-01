{-# LANGUAGE OverloadedStrings #-}
module Expresso.Pretty (
      module Text.PrettyPrint.ANSI.Leijen
    , parensList
    , bracketsList
    , bracesList
    , sepBy
    , catBy
    , render
    ) where

import Text.PrettyPrint.ANSI.Leijen ( Doc, (<+>), (<//>), angles, braces, brackets
                                    , comma, dot, dquotes, hcat, hsep, indent
                                    , int, integer, double, parens, space, text, string, vcat)
import qualified Text.PrettyPrint.ANSI.Leijen as PP


{- instance IsString Doc where -}
  {- fromString = text -}

{- instance Monoid Doc where -}
  {- mempty = PP.empty -}
  {- mappend = (PP.<>) -}

bracketsList :: [Doc] -> Doc
bracketsList = brackets . hsep . PP.punctuate comma

parensList :: [Doc] -> Doc
parensList = parens . hsep . PP.punctuate comma

bracesList :: [Doc] -> Doc
bracesList = braces . hsep . PP.punctuate comma

sepBy :: Doc -> [Doc] -> Doc
sepBy d = hsep . PP.punctuate d

catBy :: Doc -> [Doc] -> Doc
catBy d = hcat . PP.punctuate d

render :: PP.Doc -> String
render doc = PP.displayS (PP.renderPretty 0.8 100 doc) []
