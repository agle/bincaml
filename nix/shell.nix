{
  isShellForCI,

  lib,
  stdenv,
  mkShell,

  # ocaml packages
  bincaml,
  bincaml_lsp,
  capstone_arm64_disas,
  odoc,
  odoc-driver,
  ocaml-lsp,
  ocamlformat,
  opam,

  # dev packages
  perf,
}:

mkShell {
  packages = [
    odoc
    odoc-driver
    ocamlformat
  ]

  ++ lib.optionals (!isShellForCI) (
    [
      bincaml_lsp
      ocaml-lsp
    ]
    ++ lib.optional stdenv.hostPlatform.isLinux perf
  )

  ++ lib.optionals (isShellForCI) [
    opam
  ];

  inputsFrom = [
    (bincaml.overrideAttrs { doCheck = true; })
    (capstone_arm64_disas.overrideAttrs { doCheck = true; })
    (bincaml_lsp.overrideAttrs { doCheck = true; })

    # including these unchanged will subtract them from the dependencies of each other:
    # https://github.com/NixOS/nixpkgs/blob/f9bb1890175874edf242921789e8e9fdfcc2023c/pkgs/build-support/mkshell/default.nix#L32-L34
    bincaml
    capstone_arm64_disas
    bincaml_lsp
  ];

  shellHook = lib.optionalString isShellForCI ''
    opam init --bare --disable-sandboxing $(mktemp -d) --quiet --no --no-setup
  '';
}
