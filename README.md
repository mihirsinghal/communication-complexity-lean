# CommunicationComplexity

A Lean 4 formalization of communication complexity theory, following Rao–Yehudayoff Chapter 1.

## Viewing the blueprint

The blueprint is a dependency graph of all definitions, lemmas, and theorems in the project.

### Online

Once the `lucy/blueprint` branch is merged into `main`, the blueprint will be built and deployed automatically to GitHub Pages on every push.

### Locally

Make sure you have the `leanblueprint` Python package installed:

```bash
pip install leanblueprint
```

Then from the root of this repo:

```bash
leanblueprint web   # builds the HTML blueprint into blueprint/web/
leanblueprint serve # serves it at http://localhost:8000
```

Open http://localhost:8000 in your browser. The **dependency graph** tab on each theorem/definition page shows what it depends on and what depends on it.

## GitHub configuration

To deploy the blueprint via GitHub Actions, follow these one-time setup steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".
