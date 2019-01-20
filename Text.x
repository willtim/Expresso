--
-- Expresso Text Library
--
let
    list    = import "List.x";

    isEmpty : Text -> Bool
            = t -> t == "";

    length : Text -> Int
           = unpack >> list.length;

    isSpace : Char -> Bool
            = c -> c == ' ';

    isNewLine : Char -> Bool
              = c -> c == '\n';

    isUpper : Char -> Bool
            = c -> c >= 'A' && c <= 'Z';

    isLower : Char -> Bool
            = c -> c >= 'a' && c <= 'z';

    isDigit : Char -> Bool
            = c -> c >= '0' && c <= '9';

    isAlpha : Char -> Bool
            = c -> isUpper c || isLower c;

    isAlphaNum : Char -> Bool
               = c -> isAlpha c || isDigit c;

    concat : [Text] -> Text
           = foldr (t t' -> t <> t') "";

    -- Trim spaces from both sides of the given text
    trim : Text -> Text
         =  unpack
         >> list.dropWhile isSpace
         >> list.dropWhileEnd isSpace
         >> pack

-- Exports
in { isEmpty
   , length
   , isSpace
   , isNewLine
   , isUpper
   , isLower
   , isDigit
   , isAlpha
   , isAlphaNum
   , concat
   , trim
   }
