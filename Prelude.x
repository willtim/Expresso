--
-- Expresso Prelude
--
let
    ------------------------------------------------------------
    -- List operations

    concat = xss: foldr (xs: ys: xs ++ ys) [] xss;
    intersperse = sep: xs:
        let f = x: xs: (if null xs then [x] else x :: sep :: xs)
        in foldr f [] xs;
    intercalate = xs: xss: concat (intersperse xs xss);

    ------------------------------------------------------------
    -- Dynamic binding

    withOverride = overrides: f: self: overrides (f self);
    mkOverridable = f: { override_ = overrides: (withOverride overrides f) | fix f};

    -- our exported override function
    override = r: overrides: mkOverridable (r.override_ overrides)


-- Exports
in { concat
   , intercalate
   , intersperse
   , mkOverridable
   , override
   }
