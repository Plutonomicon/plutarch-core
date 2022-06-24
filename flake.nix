{
  description = "Plutarch 2.0 (WIP)";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.simpleFlake {
      inherit self nixpkgs;
      name = "plutarch-core";
      shell = ./shell.nix;
    };
}
