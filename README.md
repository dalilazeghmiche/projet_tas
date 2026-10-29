# Projet TAS — Évaluateur et Typeur d'un λ-calcul enrichi

Projet du cours **TAS (Typage et Analyse Statique)** — Master 2 STL, Sorbonne Université.

Implémentation en **OCaml** d'un évaluateur et d'un typeur pour un λ-calcul,
enrichi progressivement (entiers, listes, `let`, `fix`, traits impératifs…).

## Compilation et exécution

Prérequis : OCaml et dune.

```bash
dune build
dune exec ./bin/main.exe
```

## Organisation du code

| Fichier | Contenu |
|---|---|
| `bin/syntaxe.ml` | Syntaxe des termes et des types, pretty printers |
| `bin/eval.ml` | Évaluateur : alpha-conversion, substitution, réduction Left-to-Right Call-by-Value |
| `bin/typeur.ml` | Typeur : génération d'équations, unification, inférence de types |
| `bin/main.ml` | Exemples et tests |

## Avancement

- [x] **Partie 2 — λ-calcul simplement typé**
  - [x] Syntaxe et pretty printer
  - [x] Alpha-conversion (convention de Barendregt)
  - [x] Substitution
  - [x] Réduction LtR-CbV (une étape, puis évaluation complète avec timeout)
  - [x] Génération d'équations, unification (avec timeout), inférence
- [ ] **Partie 3 — Entiers, listes, `let`, `fix`, let-polymorphisme**
- [ ] **Partie 4 — Traits impératifs (`ref`, `!`, `:=`), polymorphisme faible**
- [ ] **Partie 5 — Extensions**


