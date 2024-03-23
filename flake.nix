{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = ins : ins.flake-utils.lib.eachDefaultSystem (system : let
    pkgs = import ins.nixpkgs { inherit system; };
  in {
    devShells.default = pkgs.mkShell {
      buildInputs = with pkgs; [ elan lean4 ];
    };
  });
}
