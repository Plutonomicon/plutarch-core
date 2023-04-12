{ mkDerivation, base, generics-sop, lib, text, transformers }:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [ base generics-sop text transformers ];
  license = lib.licenses.mit;
}
