# dafny-training
Some examples of Dafny code to support training sessions

# Install Dafny/VSCode

You should install the [Dafny VsCode plugin](https://marketplace.visualstudio.com/items?itemName=correctnessLab.dafny-vscode).

The installer may prompt you to agree to install Dafny 3.0.0, Z3 and change some permissions.

You may configure the plugin to verify `on save` only (set the Dafny plugin settings in VSCode) as otherwise live and continuous verification can alter performance.

# Dafny CLI

In the session we may use the CLI (e.g. for compile/run).
You can use the Dafny executubla bundled in the plugin located 
at `$HOME/.vscode/extensions/correctnesslab.dafny-vscode-1.4.0/out/dafnyLanguageServer/Dafny.dll`.
To run the `.dll` on non-windows system, you'll have to install `dotnet`.
You can then create an `alias` for `dafny` 

```zsh
alias dafny=`dotnet ../../.vscode/extensions/correctnesslab.dafny-vscode-1.4.0/out/dafnyLanguageServer/Dafny.dll`
```

Alternatively, you can install the [Dafny 3.0.0 latest release](https://github.com/dafny-lang/dafny/releases/tag/v3.0.0) for your system which provide a `dafny` executable (the VSCode plugin also runs Dafny 3.0.0).
There is no conflict between the plugin version and another one that you install manually. The plugin configuration defaults to use the Dafny executables bundled with the plugin.

Make sure you add the path to the Dafny executable to your paths.
# Checking your installation

## Checking Plugin

1. Clone/fork this repository.
2. Open the file `training1.dfy` in session1
3. The `Problems` tab should display a couple of information (`decreases` and another related to `triggers`). If this is the case you should be all set.

## Checking CLI


In a terminal, the command `dafny /help` should output something like:
```zsh
% dafny -version
Dafny 3.0.0.30203
```

You can `cd` to the `sessions` directoty and try the following commands:

```zsh
% dafny /dafnyVerify:1 compile:0 /trace training1.dfy
```

On my computer this results in (path names may differ on your system):

```zsh
dafny /dafnyVerify:1 /compile:0 /trace training1.dfy 
Parsing training1.dfy
Coalescing blocks...
Inlining...

Running abstract interpretation...
  [0.056181 s]
[TRACE] Using prover: /Users/franck/local/dafny3.0.0/z3/bin/z3

Verifying Impl$$_module.__default.abs ...
  [0.395 s, 1 proof obligation]  verified

Verifying Impl$$_module.__default.max ...
  [0.066 s, 1 proof obligation]  verified

Verifying Impl$$_module.__default.ex1 ...
  [0.066 s, 3 proof obligations]  verified

Verifying Impl$$_module.__default.find ...
  [0.073 s, 6 proof obligations]  verified

Verifying CheckWellformed$$_module.__default.sorted ...
  [0.071 s, 2 proof obligations]  verified

Verifying Impl$$_module.__default.unique ...
  [0.063 s, 1 proof obligation]  verified

Verifying Impl$$_module.__default._default_Main ...
  [0.085 s, 6 proof obligations]  verified

Verifying CheckWellformed$$_module.__default.proveBCantBeLongerThanA ...
  [0.086 s, 1 proof obligation]  verified

Verifying Impl$$_module.__default.proveBCantBeLongerThanA ...
  [0.069 s, 12 proof obligations]  verified

Dafny program verifier finished with 9 verified, 0 errors
```

## Note

On MacOSX, if you have manually installed the Dafny 3.0.0  release you may encounter some permission issues on MacOSX.
In that case, you may have to _allow_ several files to be executable (this is via the _Security_ widget in the _Preferences_.)

