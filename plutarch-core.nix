{ mkDerivation, base, lib }:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [ base ];
  license = lib.licenses.mit;
}
