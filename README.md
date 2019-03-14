r-fairdist
==========

Fair Resource Distribution Algorithm

The r-fairdist project implements an algorithm to share a dynamic set of
resources fairly with a dynamic set of peers. For any given finite resource, it
provides a way to request shares of this resource and thus distribute the
resource amongst users. It tries to maximize the amount each user gets, while
retaining a reserve so any further user joining the system is always guaranteed
a specific share of the total. This guarantee keeps the system fair and
prevents malicious allocations from exploiting the resource pool.

### Project

 - **Website**: <https://r-util.github.io/r-fairdist>
 - **Bug-Tracker**: <https://github.com/r-util/r-fairdist/issues>

### Requirements:

The requirements for this project are:

 * `rustc >= 1.32.0`
 * `std >= 1.32.0`

### Build

To build the project, run:

```sh
cargo build
```

### Repository:

 - **web**:   <https://github.com/r-util/r-fairdist>
 - **https**: `https://github.com/r-util/r-fairdist.git`
 - **ssh**:   `git@github.com:r-util/r-fairdist.git`

### License:

 - **Apache-2.0** OR **LGPL-2.1-or-later**
 - See AUTHORS file for details.
