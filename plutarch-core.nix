{ mkDerivation, base, generics-sop, lib }:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [ base generics-sop ];
  license = lib.licenses.mit;
}
