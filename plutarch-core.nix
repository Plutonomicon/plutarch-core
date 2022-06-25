{ mkDerivation, base, lib, generics-sop, data-fix }:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  libraryHaskellDepends = [
    base
    generics-sop
    data-fix
  ];
  testHaskellDepends = [ ];
  license = lib.licenses.mit;
  hydraPlatforms = lib.platforms.none;
  doHaddock = false;
  doCheck = false;
}
