--
-- Expresso List Library
--
let
    map         = f -> foldr (x xs -> f x :: xs) [];
    filter      = f -> foldr (x xs -> if f x then (x::xs) else xs);
    length      = foldr (const (n -> 1 + n)) 0;
    foldl       = f z xs -> foldr (x xsf r -> xsf (f r x)) id xs z;
    reverse     = foldl (xs x -> x :: xs) [];
    concat      = xss -> foldr (xs ys -> xs ++ ys) [] xss;
    intersperse = sep xs ->
        let f   = x xs -> (if null xs then [x] else x :: sep :: xs)
        in foldr f [] xs;
    intercalate = xs xss -> concat (intersperse xs xss);

    dropWhile = p -> xs -> foldr (x r b -> if b && p x then r True else x::r False) (const []) xs True;

    dropWhileEnd = p -> foldr (x xs -> if null xs && p x then [] else x :: xs) []

-- Exports
in { map
   , filter
   , length
   , foldl
   , reverse
   , concat
   , intercalate
   , intersperse
   , dropWhile
   , dropWhileEnd
   }
