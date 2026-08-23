# vendor/ckl2026

Literature and lemma interface for

> Yuxu Chen, Hui Kou, Zhenchao Lyu.
> *Finite-valuation approximable structures: a solution to the Jung–Tix
> problem of probabilistic powerdomains.* arXiv:2608.03073, 2026.

## License / status

The mathematics is that of Chen–Kou–Lyu (Sichuan University). The
repository URL `https://github.com/ChanYuxu/Recent-Progress-on-Domain-Theory`
was **not publicly fetchable** (GitHub 404, 2026-08-22). No third-party
Lean sources are copied here.

The Lean mechanization of Lemmas 6.8–6.10 used by this package lives in
`../../Quantum/Saturation.lean` (Apache-2.0, Lars Warren Ericson).
See `NOTICE` and `../../PROVENANCE.md`.

## Named lemmas (as used)

| CKL | Lean |
| --- | --- |
| Def. 2.1 (finite separator) | `FinitelySeparated` |
| Lemma 6.8 | `finitelySeparated_wayBelow` |
| Lemma 6.3 / 6.9 (flattening) | `saturation_flattening` |
| Thm. 6.10(ii) (saturation) | used in `qDInf_isOmegaQVA` |
