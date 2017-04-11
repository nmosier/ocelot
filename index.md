---
title: Ocelot
---

# Ocelot
<h2 class="subhead">A Solver-Aided Relational Logic DSL</h2>

<img class="logo" src="img/ocelot.jpg" />

Ocelot provides an embedding of relational logic (like [Alloy](http://alloy.mit.edu))
in the [Rosette](http://emina.github.io/rosette/) solver-aided programming language.
The embedded allows both solving and verification of relational specifications,
as well as *synthesis* of relational specifications,
and integration with other Rosette constraints.

Ocelot is developed at the [University of Washington](http://cs.washington.edu)
by [James Bornholt](http://homes.cs.washington.edu/~bornholt/)
and [Emina Torlak](http://homes.cs.washington.edu/~emina/).

### Getting started

Ocelot is available through the [Racket](https://racket-lang.org) package manager:

    raco pkg install ocelot

The [documentation](#) contains a quick start guide to constructing Ocelot programs.
Ocelot is similar to [Alloy](http://alloy.mit.edu),
and so many of the principles and examples from that language
will translate well.

### Get the code

Ocelot is available [on GitHub](https://github.com/jamesbornholt/ocelot).