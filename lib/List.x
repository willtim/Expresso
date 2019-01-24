--
-- Expresso additional List operations
--
let

    {..} = import "Prelude.x";

    reverse
        : forall a. [a] -> [a]
        = foldl (xs x -> x :: xs) [];

    tails
        : forall a. [a] -> [[a]]
        = fix (r xs ->
                  case uncons xs of
                    { Nothing{} -> [[]]
                    , Just{tail=xs'} -> xs :: r xs'
                    });

    intersperse
        : forall a. a -> [a] -> [a]
        = sep xs ->
        let f   = x xs -> (if null xs then [x] else x :: sep :: xs)
        in foldr f [] xs;

    intercalate
        : forall a. [a] -> [[a]] -> [a]
        = xs xss -> concat (intersperse xs xss);

    dropWhile
        : forall a. (a -> Bool) -> [a] -> [a]
        = p -> xs -> foldr (x r b ->
        if b && p x then r True else x::r False) (const []) xs True;

    dropWhileEnd
        : forall a. (a -> Bool) -> [a] -> [a]
        = p -> foldr (x xs -> if null xs && p x then [] else x :: xs) [];

    takeWhile
        : forall a. (a -> Bool) -> [a] -> [a]
        = p -> foldr (x xs -> if p x then x :: xs else []) [];

    takeWhileEnd
        : forall a. (a -> Bool) -> [a] -> [a]
        = p -> reverse << takeWhile p << reverse;

    isPrefixOf
        : forall a. Eq a => [a] -> [a] -> Bool
        = fix (r xs ys ->
                  case uncons xs of
                    { Nothing{} -> True
                    , Just {head=x, tail=xs'} ->
                        case uncons ys of
                          { Nothing{} -> False
                          , Just {head=y, tail=ys'} ->
                              x==y && r xs' ys'
                          }
                    });

    isSuffixOf
        : forall a. Eq a => [a] -> [a] -> Bool
        = xs ys -> isPrefixOf (reverse xs) (reverse ys);

    stripPrefix
        : forall a. Eq a => [a] -> [a] -> Maybe [a]
        = fix (r xs ys ->
                  case uncons xs of
                     { Nothing{} -> Just ys
                     , Just{head=x,tail=xs'} ->
                       case uncons ys of
                         { Nothing{} -> Nothing{}
                         , Just {head=y, tail=ys'} ->
                             if x==y then r xs' ys' else Nothing{}
                         }
                   });

    stripSuffix
        : forall a. Eq a => [a] -> [a] -> Maybe [a]
        = xs ys -> stripPrefix (reverse xs) (reverse ys);

    dropPrefix
        : forall a. Eq a => [a] -> [a] -> [a]
        = xs ys -> fromMaybe ys (stripPrefix xs ys);

    dropSuffix
        : forall a. Eq a => [a] -> [a] -> [a]
        = xs ys -> fromMaybe ys (stripSuffix xs ys);

    zipWith
        : forall a b c. (a -> b -> c) -> [a] -> [b] -> [c]
        = f -> fix (r xs ys ->
                      case uncons xs of
                         { Nothing{} -> []
                         , Just{head=x,tail=xs'} ->
                           case uncons ys of
                             { Nothing{} -> []
                             , Just {head=y, tail=ys'} ->
                                 f x y :: r xs' ys'
                             }
                       });

    zip : forall a b. [a] -> [b] -> [{l:a, r:b}]
        = zipWith (a b -> { l = a, r = b });


    replace
        : forall a. Eq a => [a] -> [a] -> [a] -> [a]
        = fix (r from to xs ->
            if null from then xs
            else case stripPrefix from xs of
              { Just xs'  -> to ++ r from to xs'
              , Nothing{} -> case uncons xs of
                               { Nothing{} -> []
                               , Just{head=x, tail=xs'} ->
                                   x :: r from to xs'
                               }})

   -- Prelude re-exports
in { foldr
   , null
   , map
   , filter
   , length
   , foldl
   , concat

   -- Exports
   , reverse
   , tails
   , intersperse
   , intercalate
   , dropWhile
   , dropWhileEnd
   , takeWhile
   , takeWhileEnd
   , isPrefixOf
   , isSuffixOf
   , stripPrefix
   , stripSuffix
   , dropPrefix
   , dropSuffix
   , zipWith
   , zip
   , replace
   }
