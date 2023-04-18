{ mkDerivation, base, lib, sop-core }:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [ base sop-core ];
  license = lib.licenses.mit;
}
