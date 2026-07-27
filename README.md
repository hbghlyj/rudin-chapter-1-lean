# Rudin and Wheeden exercise formalizations

This repository contains Lean formalizations and accompanying LaTeX solutions for selected exercises from Rudin and Wheeden.

The configured Lean libraries are:

- `RudinChapter1`
- `RudinChapter2`
- `RudinChapter3`
- `RudinChapter4`
- `RudinChapter5`
- `RudinChapter6`
- `WheedenChapter1`
- `WheedenChapter2`

Build all configured libraries and default targets with:

```sh
lake build RudinChapter1 RudinChapter2 RudinChapter3 RudinChapter4 RudinChapter5 RudinChapter6 WheedenChapter1 WheedenChapter2
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
