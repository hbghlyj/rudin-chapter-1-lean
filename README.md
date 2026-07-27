# Rudin and Wheeden exercise formalizations

This repository contains Lean formalizations and accompanying LaTeX solutions for selected exercises from Rudin and Wheeden.

The configured Lean libraries comprise `RudinChapter1` through
`RudinChapter6`, `WheedenChapter1` and `WheedenChapter2`,
`IntroSmoothManifoldsChapter1` through `IntroSmoothManifoldsChapter22`, and
the three review libraries `IntroSmoothManifoldsAReviewofTopology`,
`IntroSmoothManifoldsBReviewofLinearAlgebra`, and
`IntroSmoothManifoldsCReviewofCalculus`.

Build all configured libraries and default targets with:

```sh
lake build
```

Chapter 1 Lean sources are in `RudinChapter1/`; the corresponding LaTeX document remains `rudin_ch1_exercises.tex`.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
