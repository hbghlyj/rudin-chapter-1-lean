# LaTeX-to-Lean inventory

Each LaTeX source has a configured Lean library, a matching default target, and a `Main.lean` entry point. The table records the repository mapping and the present formalization status. “Partial” means that the library builds and contains proved supporting results, but not every proposition/exercise appearing in the LaTeX has yet been represented faithfully as a named Lean theorem.

| LaTeX source | Lean library | Status |
|---|---|---|
| `rudin_ch1_exercises.tex` | `RudinChapter1/` | Formalized |
| `rudin_ch2.tex` | `RudinChapter2/` | Partial |
| `rudin_ch3.tex` | `RudinChapter3/` | Partial |
| `rudin_ch4.tex` | `RudinChapter4/` | Partial |
| `rudin_ch5.tex` | `RudinChapter5/` | Partial |
| `rudin_ch6.tex` | `RudinChapter6/` | Partial |
| `wheeden_ch1.tex` | `WheedenChapter1/` | Partial |
| `wheeden_ch2.tex` | `WheedenChapter2/` | Partial (boundedness and continuity-at-zero steps formalized; infinite variation remains) |
| `IntroSmoothManifolds_ch1.tex` | `IntroSmoothManifoldsChapter1/` | Partial |
| `IntroSmoothManifolds_ch2.tex` | `IntroSmoothManifoldsChapter2/` | Partial |
| `IntroSmoothManifolds_ch3.tex` | `IntroSmoothManifoldsChapter3/` | Partial |
| `IntroSmoothManifolds_ch4.tex` | `IntroSmoothManifoldsChapter4/` | Partial |
| `IntroSmoothManifolds_ch5.tex` | `IntroSmoothManifoldsChapter5/` | Partial |
| `IntroSmoothManifolds_ch6.tex` | `IntroSmoothManifoldsChapter6/` | Partial |
| `IntroSmoothManifolds_ch7.tex` | `IntroSmoothManifoldsChapter7/` | Partial |
| `IntroSmoothManifolds_ch8.tex` | `IntroSmoothManifoldsChapter8/` | Partial |
| `IntroSmoothManifolds_ch9.tex` | `IntroSmoothManifoldsChapter9/` | Partial |
| `IntroSmoothManifolds_ch10.tex` | `IntroSmoothManifoldsChapter10/` | Partial |
| `IntroSmoothManifolds_ch11.tex` | `IntroSmoothManifoldsChapter11/` | Exercise 11.2 formalized |
| `IntroSmoothManifolds_ch12.tex` | `IntroSmoothManifoldsChapter12/` | Partial |
| `IntroSmoothManifolds_ch13.tex` | `IntroSmoothManifoldsChapter13/` | Partial |
| `IntroSmoothManifolds_ch14.tex` | `IntroSmoothManifoldsChapter14/` | Partial |
| `IntroSmoothManifolds_ch15.tex` | `IntroSmoothManifoldsChapter15/` | Partial |
| `IntroSmoothManifolds_ch16.tex` | `IntroSmoothManifoldsChapter16/` | Partial |
| `IntroSmoothManifolds_ch17.tex` | `IntroSmoothManifoldsChapter17/` | Partial |
| `IntroSmoothManifolds_ch18.tex` | `IntroSmoothManifoldsChapter18/` | Partial |
| `IntroSmoothManifolds_ch19.tex` | `IntroSmoothManifoldsChapter19/` | Partial |
| `IntroSmoothManifolds_ch20.tex` | `IntroSmoothManifoldsChapter20/` | Partial |
| `IntroSmoothManifolds_ch21.tex` | `IntroSmoothManifoldsChapter21/` | Source statement is incomplete; only generic supporting facts are currently formalized |
| `IntroSmoothManifolds_ch22.tex` | `IntroSmoothManifoldsChapter22/` | Partial |
| `IntroSmoothManifolds_A.tex` | `IntroSmoothManifoldsAReviewofTopology/` | Proposition A.16 formalized |
| `IntroSmoothManifolds_B.tex` | `IntroSmoothManifoldsBReviewofLinearAlgebra/` | Exercises B.9, B.13, B.22(c), and B.49 formalized; other exercises partial/prose-only |
| `IntroSmoothManifolds_C.tex` | `IntroSmoothManifoldsCReviewofCalculus/` | Propositions C.3 and the inverse-derivative content of C.4 formalized |

## Configuration and verification

The 33 `[[lean_lib]]` entries in `lakefile.toml` are in the same order as, and exactly equal to, the 33 `defaultTargets`. Every library has a `Main.lean`. The complete default build succeeds, and the project-wide Lean source scan contains no `sorry`, `admit`, `exact?`, or `skip`.
