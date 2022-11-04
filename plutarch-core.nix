{ mkDerivation, base, generics-sop, lib, text }:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [ base generics-sop text ];
  testHaskellDepends = [ base generics-sop text ];
  license = lib.licenses.mit;
}
