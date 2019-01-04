{ mkDerivation, base, containers, directory, filepath, hashable
, haskeline, mtl, parsec, stdenv, tasty, tasty-hunit
, template-haskell, terminfo, text, unordered-containers, wl-pprint
}:
mkDerivation {
  pname = "expresso";
  version = "0.1.1.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base containers directory filepath hashable haskeline mtl parsec
    template-haskell terminfo text unordered-containers wl-pprint
  ];
  executableHaskellDepends = [
    base containers directory filepath hashable haskeline mtl parsec
    terminfo text unordered-containers wl-pprint
  ];
  testHaskellDepends = [
    base containers directory filepath hashable haskeline mtl parsec
    tasty tasty-hunit terminfo text unordered-containers wl-pprint
  ];
  description = "A simple expressions language based on row types";
  license = stdenv.lib.licenses.bsd3;
}
