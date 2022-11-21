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
  isExecutable = true;
  libraryHaskellDepends = [
    base
    generics-sop
    text
    text-builder-linear
    transformers
  ];
  executableHaskellDepends = [
    base
    directory
    generics-sop
    text
    text-builder-linear
    transformers
  ];
  license = lib.licenses.mit;
  mainProgram = "examples";
}
