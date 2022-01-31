/// testing 2
module gyre;

import std.stdio;

/// bla bla foo bla
void foo() {
	writeln("Edit source/app.d to start your project.");
}

///
unittest {
	foo();
	assert(1 + 1 == 2);
}
