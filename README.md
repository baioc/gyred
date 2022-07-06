GyreD
====

<!-- XXX: if only we had [separate badges for matrix testing](https://github.community/t/separate-workflow-badges-when-using-matrix-testing-possible/16708/16) -->
[![pipeline status](https://github.com/baioc/gyred/actions/workflows/ci.yml/badge.svg)](https://github.com/baioc/gyred/actions/workflows/ci.yml)
[![latest version](https://img.shields.io/github/v/tag/baioc/gyred?color=blue&label=docs&logo=llvm)](https://baioc.github.io/gyred/gyre.html)

This is a reference implementation of [Gyre](https://baioc.github.io/gyred/gyre.html), a compiler IR designed as a practical "linguistic switchbox", or [UNCOL](https://en.wikipedia.org/wiki/UNCOL).

As such, the IR should be able to efficiently accommodate many high-level languages and target architectures.
In order to test this, this repository ~~contains~~ will contain multiple compilers using the same middle-end infrastructure.


Work In Progress
----

This is an early-stage prototype of an IR designed as part of my Bachelor thesis, which provides an extensive survey on compilers, portable IRs and the UNCOL solution to ["the problem of programming communication with changing machines"](https://doi.org/10.1145/368892.368915), also known as ["the compiler construction problem"](http://www.tendra.org/Macrakis93-uncol.pdf).

If you are looking for a ready-to-use optimization framework, a full compiler, or benchmark results for any of these, **come back later**.
In that case, I suggest using GitHub to watch this repository's releases, and/or star it so I know there are people interested.
In any case, here is an [example](https://gist.github.com/baioc/a063d120d23d6b1566eea28be067525e) of the current IR builder API.

Still, here are some figures from my thesis, to spark your curiosity.
Check out [the docs](https://baioc.github.io/gyred/gyre.html) for more information.

| Logical structure of an optimizing compiler | UNCOL as a linguistic switchbox |
|:---:|:---:|
| ![compiler-structure](https://user-images.githubusercontent.com/27034173/177571214-accedb7d-d211-4a4a-bffe-efc51a3d8438.png) | ![uncol-solution](https://user-images.githubusercontent.com/27034173/177571231-61025533-e94f-4f37-a377-bc88dbd70615.png) |

| Gyre subgraph with explicit concurrency | Mapping of classic SSACFG constructs |
|:---:|:---:|
| ![gyre-fork-join](https://user-images.githubusercontent.com/27034173/177571300-dbefe896-8113-4dc5-bd60-30e0fb6b4b79.png) | ![gyre-vs-ssa-cfg](https://user-images.githubusercontent.com/27034173/177571350-e7d7f614-162f-4f83-a025-4b6915288b23.png) |

| Memory operations in Gyre | IR types and macros |
|:---:|:---:|
| ![gyre-state](https://user-images.githubusercontent.com/27034173/177571308-0d8b1686-322f-4de0-aae7-8c83f9a33ce9.png) | ![gyre-typed](https://user-images.githubusercontent.com/27034173/177571327-fd4f795f-2faa-4ea8-9285-bc0264e47530.png) |


Development
----

These are the configuration files which I use to build, test and debug this project in VSCode.

The only tool needed is [DUB](https://dub.pm/), but I also recommend the [awesome VSCode extensions by WebFreak](https://marketplace.visualstudio.com/items?itemName=webfreak.dlang-bundle).

### `tasks.json`

```json
{
    "version": "2.0.0",
    "tasks": [
        {
            "label": "dub: Run unit tests",
            "group": {
                "kind": "test",
                "isDefault": true
            },
            "type": "shell",
            "command": "dub test --coverage",
            "problemMatcher": {
                "owner": "d",
                "fileLocation": ["relative", "${workspaceFolder}"],
                "pattern": {
                    "regexp": "^(.*)@(.*)\\((\\d+)\\):\\s+(.*)$",
                    "code": 1,
                    "file": 2,
                    "location": 3,
                    "message": 4,
                }
            },
            "presentation": {
                "echo": false,
                "clear": true,
            },
        },
        {
            "label": "dub: Build project docs",
            "group": {
                "kind": "build",
                "isDefault": true
            },
            "type": "shell",
            "command": "dub run adrdox@2.5.2 -- . -i -o docs",
            "problemMatcher": {
                "owner": "d",
                "fileLocation": ["relative", "${workspaceFolder}"],
                "pattern": {
                    "regexp": "^(.*)\\((\\d+,\\d+)\\):\\s+(Error|Warning):\\s+(.*)$",
                    "file": 1,
                    "location": 2,
                    "severity": 3,
                    "message": 4,
                }
            },
            "presentation": {
                "echo": false,
                "clear": true,
                "reveal": "silent",
            },
        }
    ],
}
```

### `launch.json`

```json
{
    "version": "0.2.0",
    "configurations": [
        {
            "name": "Debug application",
            "type": "gdb",
            "request": "launch",
            "cwd": "${workspaceRoot}",
            "target": "gyred",
        },
        {
            "name": "Debug unittest",
            "type": "gdb",
            "request": "launch",
            "cwd": "${workspaceRoot}",
            "target": "gyred-test-unittest",
        },
    ]
}
```
