{ mkDerivation, base, containers, directory, filepath, hashable
, haskeline, mtl, parsec, stdenv, tasty, tasty-hunit, text
, unordered-containers, wl-pprint
}:
mkDerivation {
  pname = "expresso";
  version = "0.1.1.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base containers directory filepath hashable mtl parsec text
    unordered-containers wl-pprint
  ];
  testHaskellDepends = [
    base containers directory filepath hashable haskeline mtl parsec
    tasty tasty-hunit text unordered-containers wl-pprint
  ];
  description = "A simple expressions language based on row types";
  license = stdenv.lib.licenses.bsd3;
}
