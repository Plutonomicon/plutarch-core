{ mkDerivation, base, lib, generics-sop }:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  libraryHaskellDepends = [
    base generics-sop
  ];
  testHaskellDepends = [];
  license = lib.licenses.mit;
  hydraPlatforms = lib.platforms.none;
  doHaddock = false;
  doCheck = false;
}
