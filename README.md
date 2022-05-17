GyreD
====

<!-- XXX: if only we had [separate badges for matrix testing](https://github.community/t/separate-workflow-badges-when-using-matrix-testing-possible/16708/16) -->
[![pipeline status](https://github.com/baioc/gyred/actions/workflows/ci.yml/badge.svg)](https://github.com/baioc/gyred/actions/workflows/ci.yml)
[![latest version](https://img.shields.io/tokei/lines/github/baioc/gyred?color=blue&label=docs&logo=llvm)](https://baioc.github.io/gyred/gyre.html)

This is a reference implementation of [Gyre](https://baioc.github.io/gyred/gyre.html), a compiler IR designed as a practical "linguistic switchbox", or [UNCOL](https://www.osdata.com/topic/language/uncol.htm).

As such, the IR should be able to efficiently accommodate many high-level languages and target architectures.
In order to test this, this repository contains multiple compilers, all using the same middle-end infrastructure.
