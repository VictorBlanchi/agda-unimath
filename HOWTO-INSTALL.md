# INSTALL

To use the `agda-unimath` library, you will need to have Agda and a code editor
set up. This guide provides instructions for installing Agda as well as specific
setup instructions for the editors Emacs and Visual Studio Code. By following
theese step-by-step directions, you will create a tailored working environment
for using the library. Additionally, we provide instructions for setting up your
environment for making contributions to the library.

## Getting a copy of the library

Get a copy of our library on your machine with `git` using

```shell
git clone git@github.com:UniMath/agda-unimath.git
```

or by going to the [GitHub page](https://github.com/UniMath/agda-unimath) and
manually downloading it.

## Installing Agda

The `agda-unimath` library is built and verified with Agda 2.6.3, and we provide
two methods for installation: with or without the package manager Nix. Nix
streamlines the installation of Agda and its dependencies, providing a
consistent and reproducible environment for the library across different
systems.

### Without Nix

To install Agda 2.6.3 without Nix, follow the
[installation guide](https://agda.readthedocs.io/en/latest/getting-started/installation.html)
provided on the Agda documentation page.

### With Nix

The library comes with a development shell described in the `flake.nix` file. To
activate the shell, open a terminal in the directory where you cloned the
library, and run:

```shell
nix develop
```

Once you've activated the shell, launch your editor from within it by running
`code` or `emacs`. This ensures your editor recognizes the Agda installation.

## Tutorials for Agda

If you're new to Agda, there are several resources available to help you learn
the basics and become proficient in using the language. We recommend starting
with the
[list of tutorials](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html)
provided on the Agda documentation page.

## Editor setup

We recommend either [Emacs](https://www.gnu.org/software/emacs/) or
[Visual Studio Code](https://code.visualstudio.com/) (VSCode) as your editor
when working with the `agda-unimath` library. Both editors offer support for
Agda development, and the choice between them is largely a matter of personal
preference. Below, you'll find setup instructions for each editor to help you
configure your preferred environment for working with the library.

### Emacs

#### Agda mode using Nix

If you installed Agda using Nix, add the following snippet to your `.emacs` file
to use the correct `agda2-mode` provided by the development environment:

```elisp
(when (executable-find "agda-mode")
  (load-file (let ((coding-system-for-read 'utf-8))
               (shell-command-to-string "agda-mode locate"))))
```

This is a modified version of the usual `agda2-mode` setup provided by Agda,
except it checks if Agda is available, so that it doesn't cause errors when
opening Emacs outside the project.

#### Literate Agda files

The `agda-unimath` library is written in literate markdown Agda. Add the
following line to your `.emacs` file to enable Emacs to handle literate Agda
files with the `.lagda.md` extension:

```elisp
(setq auto-mode-alist (cons '("\\.lagda.md$" . agda2-mode) auto-mode-alist))
```

#### Special symbols

The `agda-unimath` library employs two notations for the identity type:
Martin-Löf's original notation `Id` and an infix notation `_＝_`. The infix
notation's equals sign is not the standard one, but rather the
[full width equals sign](https://codepoints.net/U+ff1d). Observe that the full
width equals sign is slightly wider, and is highlighted in blue just like all
the other defined constructions in Agda. To type the full width equals sign in
Agda's Emacs Mode, you need to add it to your Agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Press the `INS` key
- Type the regular equals sign `=` in the Key sequence field.
- Press the `INS` key
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the full
width equals sign `＝`. While you're at it, you can also add the key sequence
`yo` to obtain the Japanese symbol `ょ` for the Yoneda embedding.

#### 80-character limit

The `agda-unimath` library maintains an 80-character limit on the length of most
lines in the source code (see [CODINGSTYLE](CODINGSTYLE.md#character-limit) for
a list of exceptions). This limit is to improve readability, both in your
programming environment and on our website. To display a vertical ruler marking
the 80th column in Emacs, add:

```elisp
(add-hook 'prog-mode-hook #'display-fill-column-indicator-mode)
```

to your `.emacs` file.

### VSCode

The `agda-unimath` library comes with a predefined VSCode workspace. Open the
folder main repository folder in VSCode, and it should automatically recognize
the workspace and apply the appropriate settings.

#### Extensions

A collection of recommended extensions is included with the workspace to
streamline your experience while working with the library. These extensions
should be automatically suggested to you when you open the repository in VSCode.

##### Agda mode

One essential extension for interacting with Agda is
[`agda-mode`](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode).
After installing this extension, you'll be able to verify `.lagda.md` files by
opening them and using the `C-c C-l` command. For a full list of commands, see
the extension's reference page.

#### Special characters

The VSCode workspace adds snippets for inserting special symbols like `＝` and
`ょ`, since there's currently no way to add these to Agda's input mode in
VSCode.

To insert these symbols in the editor, follow these steps:

1. Begin typing one of the activation sequences listed below.
2. When the symbol appears as a greyed-out character in your editor, press `TAB`
   to insert it.

- `＝`: Type `Id` or `equals`
- `ょ`: Type `yoneda`
- `⧄`: Type `diagonal` or `lifting`

These snippets are defined in `.vscode/agda.code-snippets`.

#### Autoformatting

For your convenience, the VSCode workspace configures several automatic
formatting functions. These functions continuously correct minor formatting
mistakes, ensuring a smoother coding experience.

### Note on the library's use of Unicode characters

This library relies heavily on Unicode characters, so it's important to use a
font family with comprehensive Unicode support in your editor. For instance, the
library utilizes the [middle dot](https://www.compart.com/en/unicode/U+00B7) `·`
and the [bullet operator](https://www.compart.com/en/unicode/U+2219) `∙`. In
some fonts, these two symbols appear identical. If you find it difficult to
distinguish between these symbols in your editor, we recommend switching to a
different font.

## After the setup

Congratulations! With Agda installed and your editor expertly configured, you're
now ready to dive into using the library.

### Verifying the library

To verify a file and its prerequisites with Agda, simply open and load it. If
you want to compile the entire library, you can run `make check` from the
repository's main folder. This generates the `everything.lagda.md` file, which
imports and verifies all files in the library.

### Contributing

We welcome and appreciate contributions from the community. If you're interested
in contributing to the `agda-unimath` library, please follow our guidelines and
best practices, as well as the instructions below to ensure a smooth setup and
workflow.

#### <a name="pre-commit-hooks"></a>Pre-commit hooks and Python dependencies

The `agda-unimath` library includes pre-commit hooks that enforce basic
formatting rules. To utilize these hooks, if you did not install your
environment using Nix, you'll need to install the `pre-commit` tool and the
hooks' Python dependencies. The easiest way to accomplish this is by using the
Python package manager `pip`.

First, make sure that you have the latest version of Python installed on your
computer. Then run the following command from the repository's main folder:

```shell
pip install -r scripts/requirements.txt
```

Now, before you submit a Pull Request (PR) next time, you can run `pre-commit`
by staging your changes and executing the command `make pre-commit` from the
repository's main folder.

To have `pre-commit` run automatically before every commit, run the following
command:

```shell
pre-commit install
```

After this, `pre-commit` will inform you of any rule violations in your
subsequent commits. For most violations, it will also automatically apply the
required changes. In such cases, simply stage the new changes and commit again.

Keep in mind that `pre-commit` is also a part of the Continuous Integration
(CI), so any PR that violates the enforced conventions will be automatically
blocked.
