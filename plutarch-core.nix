{ mkDerivation, base, generics-sop, transformers, lib }:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [ base generics-sop transformers ];
  license = lib.licenses.mit;
}
