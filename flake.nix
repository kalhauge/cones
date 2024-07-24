{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = {
    self,
    nixpkgs,
    flake-utils,
    ...
  } @ inputs: let
    haskellOverlay = pkgs: final: prev: {
      "cones" = final.callCabal2nixWithOptions "cones" "${self}/cones" "" {};
      "conedec" = final.callCabal2nixWithOptions "conedec" "${self}/conedec" "" {};
    };
    overlays = final: prev: {
      haskellPackages = prev.haskellPackages.extend (haskellOverlay final);
    };
  in
    {
      inherit haskellOverlay;
      overlays.default = overlays;
    }
    // flake-utils.lib.eachDefaultSystem
    (system: let
      hpkgs =
        (import nixpkgs {
          inherit system;
          overlays = [overlays];
        })
        .haskellPackages;
    in {
      packages = {
        default = hpkgs.cones;
        cones = hpkgs.cones;
        conedec = hpkgs.conedec;
      };
      devShells = let
        buildInputs = with hpkgs; [
          cabal-install
          ghcid
          haskell-language-server
          hpack
          fourmolu
        ];
        withHoogle = true;
      in {
        default =
          hpkgs.shellFor
          {
            name = "cones-shell";
            packages = p: [p.cones p.conedec];
            inherit buildInputs withHoogle;
          };
        conedec =
          hpkgs.shellFor
          {
            name = "conedec-shell";
            packages = p: [p.conedec];
            inherit buildInputs withHoogle;
          };
      };
    });
}
