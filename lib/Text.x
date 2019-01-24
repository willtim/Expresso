--
-- Expresso Text Library
--
let
    {..} = import "Prelude.x";
    list = import "List.x";

    isEmpty
        : Text -> Bool
        = t -> t == "";

    length
        : Text -> Int
        = unpack >> list.length;

    isSpace
        : Char -> Bool
        = c -> c == ' ';

    isNewLine
        : Char -> Bool
        = c -> c == '\n';

    isUpper
        : Char -> Bool
        = c -> c >= 'A' && c <= 'Z';

    isLower
        : Char -> Bool
        = c -> c >= 'a' && c <= 'z';

    isDigit
        : Char -> Bool
        = c -> c >= '0' && c <= '9';

    isAlpha
        : Char -> Bool
        = c -> isUpper c || isLower c;

    isAlphaNum
        : Char -> Bool
        = c -> isAlpha c || isDigit c;

    concat
        : [Text] -> Text
        = list.foldr (t t' -> t <> t') "";

    intercalate
        : Text -> [Text] -> Text
        = s -> map unpack
            >> list.intersperse (unpack s)
            >> map pack
            >> concat;

    unwords
        : [Text] -> Text
        = intercalate " ";

    isPrefixOf
        : Text -> Text -> Bool
        = s s' -> list.isPrefixOf (unpack s) (unpack s');

    isSuffixOf
        : Text -> Text -> Bool
        = s s' -> list.isSuffixOf (unpack s) (unpack s');

    stripPrefix
        : Text -> Text -> Maybe Text
        = s s' -> mapMaybe pack (list.stripPrefix (unpack s) (unpack s'));

    stripSuffix
        : Text -> Text -> Maybe Text
        = s s' -> mapMaybe pack (list.stripSuffix (unpack s) (unpack s'));

    dropPrefix
        : Text -> Text -> Text
        = s s' -> pack (list.dropPrefix (unpack s) (unpack s'));

    dropSuffix
        : Text -> Text -> Text
        = s s' -> pack (list.dropSuffix (unpack s) (unpack s'));

    replace
        : Text -> Text -> Text -> Text
        = from to xs ->
            if isEmpty from
            then error "replace: first argument must not be empty"
            else pack (list.replace (unpack from) (unpack to) (unpack xs));

    -- Trim spaces from both sides of the given text
    trim
        : Text -> Text
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
   , intercalate
   , unwords
   , isPrefixOf
   , isSuffixOf
   , stripPrefix
   , stripSuffix
   , dropPrefix
   , dropSuffix
   , replace
   , trim
   }
