Prolog for JCU
==============

This package was developed to demonstrate the ideas behind the Prolog language.
It uses a very small interpreter (*Language.Prolog.Nanoprolog*) which can be
run on its own.

This package contains an environment constructed for the Junior College at
Utrecht University. It provides a simple environment in which rules can be
defined, and proofs can be constructed interactively. The software can be
installed on a server, so students do not have to install anything on their own
machines.


Installation instructions
=========================

This software has been tested with Haskell Platform 2012.4.0.0 on Mac
OS X 10.8.2, GHC 7.4.2 (64-bit), and UHC 1.1.4, revision master@4526152fc7, timestamp 20121116 +0100 125057

To build the JCU application make sure you have the following variables in your
environment `UHC_JSCRIPT`, `UHC_UU_TC` and `UHC_NANOPROLOG`. They should point to the sources of the uhc-js library, the UU Talen & Compiler Parser combinator library and the NanoProlog library respectively.

If you trust us you can run the following command. It will install JCU and its
dependencies (but not GHC or UHC!!!) in the current working directory.

``` shell
ruby <(curl -s https://raw.github.com/gist/4117600/install-jcu.rb)
```


Usage instructions
==================
Just open the index.html file after you have run `make`.


Using
-----
After logging in, the main screen is visible. It is divided in two sections.
On the left-hand side we have the proof tree and on the right-hand side
the list of rules.
(TODO: Finish this bit)
