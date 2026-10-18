# Bonn Lean Course WiSe 26/27

## In this repository

You will find the Lean files in the `LeanCourse26` directory:
* The `Lectures` folder contains all lectures (we will post 2 versions of each lecture file: one before class, and one after class with the comments we wrote during class)
* The `Assignments` folder contains the assignments that you have to hand in via eCampus.

## Installation

* These [instructions](https://lean-lang.org/install/) will guide you through the installation process.

* This will guide you to install VSCode (a text editor which supports Lean) and Lean.

* As part of the **extension setup**, in the step **Set up Lean 4 project** click on **Download an existing project**, if prompted choose `Git repository URL`, and enter `https://github.com/fpvandoorn/LeanCourse26` as the URL. Then navigate to the directory where you want to download this repository, and specify a folder name. It will create a new directory with that name for you. This will download Mathlib, which will take a few minutes.
  * Make sure to *not* choose any subdirectory of a cloud storage storage (Dropbox, OneDrive, etc.)
  * Windows users are recommended to disable *Virus & threat protection* for the project folder (see below).

* When you have downloaded the repository a message appears allowing you to open the project folder.
To test that everything is working, open the repository and open the file `LeanCourse26/Test.lean`.
The file should be ready after loading a while. If you see a blue squiggle under `#eval`, Lean is running correctly.

* A useful (but optional) extension is the VSCode extension `Error Lens`. If you install this, you will see messages from Lean right in the file where you're typing.

### Windows Troubleshooting

If you have a choice between operating system, Lean works a little better on Linux/Mac/WSL than on Windows, but it also works fine on Windows.

* On Windows, you are *recommended* to disable *Virus & threat protection* for the project folder. The reason is that Windows Defender significantly increases the start time of Lean. Do this (on Windows 11) by searching in the *Start Menu* for *Virus & threat protection* > *Manage Settings* > *Add or remove exclusions* and add the project folder `LeanCourse26` (the outer one) as an excluded folder.

* On Windows, if you have any other antivirus programs running, they might slow down Lean during installation and starting up Lean. Consider temporarily disabling your antivirus program in the step *Complete the extension setup*, or exclude the project folder folder from your antivirus program permanently.

* If you get errors such as `curl: (35) schannel` or `uncaught exception: no such file or directory (error code: 2)` take a look [here](https://leanprover-community.github.io/install/project.html#troubleshooting).

### General Troubleshooting

Note: To get this repository, you will need to download Lean's mathematical library, which takes about 5 GB of storage space.

It might be tricky to get Lean running on an old laptop or a chromebook, since Lean does use a moderate amount of recourses.
<!-- You can still run Lean in your browser by using Codespaces or Gitpod, see the the instructions at the bottom of this file. -->

* If after installing the extension, the extension setup shows 5 steps, but no additional information: please close all side panels (and possibly decrease the font size). The second (important) column is hidden if there is not enough room.

* Unfortunately, the installation step, and loading Lean for the first time is very slow on Windows computers. Once Lean has finished starting up, it should be quick and responsive.

* You should not need to build Mathlib files on your computer, either during installation or updating the repository. If you notice that this is happening, try the following steps:
  * Close VSCode (if it is open).
  * Open the course folder in VS Code and open some Lean file in the course.
  * Press `∀ > Project Actions... > Fetch Mathlib Build Cache` and wait for the cache to download.
  * Wait until the command finishes with downloading and decompressing. If you get an error, run it again.
  * You might have to restart the Lean file, and then Lean should be compiling your file in less than a minute.

## Update repository

If you want to get the latest version of this repository (e.g. the latest exercises), then you can pull the changes.

* First save all files you've worked on.
* Then in the `Source Control` tab (third icon in the top-left, or `ctrl+shift+G`/`cmd+shift+G`), under `⋯` (More actions) you can press `Pull`.
  (You can also run `git pull` via the terminal.)

Note: you should *not* press `Sync`, since that will try to upload your changes to the assignment files to GitHub (you don't have the rights to do this).

## Temporary ways to use Lean

You can temporarily use Codespaces or Gitpod if you have trouble installing Lean locally. (I didn't test recently whether these work)

### Using Codespaces

You can temporarily play with Lean using GitHub codespaces. This requires a GitHub account, and you can only use it for a limited amount of time each month. If you are signed in to GitHub, click here:

<a href='https://codespaces.new/fpvandoorn/LeanCourse26' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

* Make sure the Machine type is `4-core`, and then press `Create codespace`
* After 1-2 minutes you see a VSCode window in your browser. However, it is still busily downloading mathlib in the background, so give it another few minutes (5 to be safe) and then open a `.lean` file to start.

### Using Ona

Ona (formerly Gitpod) is an alternative to codespaces that is a bit inconvenient, since it requires you to verify your phone number.

Click this button to get started:

[![Open in Ona](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/fpvandoorn/LeanCourse26)

This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get!` as above.

### Live Browser version

You can run a single Lean online in the [Live editor](https://live.lean-lang.org/#project=mathlib-stable). If you haven't managed to install Lean yet, you can use this to work on a single file (e.g. an exercise file) by copy-pasting the contents in the online editor.

Warning: this could lead to subtle errors, because the live editor might use a slightly different version of Lean and Mathlib.

## Links

* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
* [Lean website](https://www.lean-lang.org/)
* [Lean-community website](https://leanprover-community.github.io/)
* [Topics in Mathlib](https://leanprover-community.github.io/mathlib-overview.html)
* [API documentation for this course](https://florisvandoorn.com/LeanCourse26/docs/)
* [latest Mathlib API documentation](https://leanprover-community.github.io/mathlib4_docs/)
* [Tactic documentation](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
