/++
Syntax sugar for our graph API.

This module provides short names for [NodeKind] and [NodeSugar] enums.
+/
module gyre.mnemonics;

import std.traits : EnumMembers, hasUDA, getUDAs;

import gyre.graph : NodeKind, AllNodes, NodeSugar;
import gyre.nodes : mnemonic;


// notice that dumping all of these as aliases in the same module top-level will
// automatically check that mnemonics are unique, failing compilation otherwise

static foreach (tag; EnumMembers!NodeKind) {
    static if (hasUDA!(AllNodes[tag], mnemonic)) {
        mixin(
            `alias ` ~ getUDAs!(AllNodes[tag], mnemonic)[0].shorthand ~ ` = `
            ~ `NodeKind.` ~ __traits(identifier, EnumMembers!NodeKind[tag]) ~ `;`
        );
    }
}

static foreach (sugar; EnumMembers!NodeSugar) {
    static if (hasUDA!(EnumMembers!NodeSugar[sugar], mnemonic)) {
        mixin(
            `alias ` ~ getUDAs!(EnumMembers!NodeSugar[sugar], mnemonic)[0].shorthand ~ ` = `
            ~ `NodeSugar.` ~ __traits(identifier, EnumMembers!NodeSugar[sugar]) ~ `;`
        );
    }
}
