{ mkDerivation
, base
, directory
, generics-sop
, lib
, text
, text-builder-linear
, transformers
}:
mkDerivation {
  pname = "plutarch-core";
  version = "0.1.0";
  src = ./.;
  isLibrary = true;
  libraryHaskellDepends = [
    base
    generics-sop
    text
    transformers
  ];
  license = lib.licenses.mit;
}
