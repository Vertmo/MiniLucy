Inductive recognize : regexp -> language alpha :=
  | recon_epsilon : recognize epsilon nil.
