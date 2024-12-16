# Comparison of CN with some other specification languages

## Overview
CN works over functions only, and each function considers other functions only
from their specification. Global variables are considered only as they are
manipulated by functions. Functions cannot access or in particular modify data
they do not declare in their specs.

AGREE allows a form of temporal logic constraints and works over *systems* with
input and output ports. Assumptions constrain input ports and guarantees
constrain output ports, based on the assumptions and guarantees of any
subcomponent. Each system considers only its assumptions and subcomponents.
AGREE is implemented as a modification to AADL.

FRET allows temporal logic constraints and works over temporal logic signals of
states of a set of variables. It does not consider implementation below this
level.

GUMBO works over threads that can receive and send events and access data
*ports*. It assumes there is a runtime system available that will run the
threads and deliver events. Threads ensure guarantees are satisfied considering
assumptions, and guarantees can include properties of data ports or that an
event of some type was actually sent. There is no analog of the frame rule
within a thread. *ports* can have constraints on values that enter or exit them.
GUMBO is also implemented as an extension to AADL.

# Representing specs in these languages in CN

## GUMBO 

GUMBO data invariants can be expressed in CN if all accessors of the variable
are known, by adding requires and ensures statements to all functions. CN
doesn't allow attaching specs to globals so this allows concluding the invariant
will always hold outside of the system, but not within CN. GUMBO translates
these variables to members in an object, which straightforwardly translates to a
struct with some functions that work on it in the usual objects-in-C style. This
will only enforce the constraints at object boundaries, but GUMBO explicitly
acknowledges this in its own code-level translations. It should be possible to
use CN's spec-level data types and constructors to make this arrangement more
conveniet, but it will still work if the well-formed constraints are
transparently inlined into every spec.

GUMBO's entry points each have various restrictions on what kinds of data they
can read, must write, and assumptions and guarantees they can assume or must
ensure. These can be implemented by careful construction of the spec of each
entry point implementation to provide read permissions only to those that can be
read and enforce writes to output and required member variables. This would be
mostly straightforward, as GUMBO's implementation language already does much of
this. GUMBO constraints for a given compute entry point are collected from
general constraints for all thread entry points as well as constraints for that
specific entry point, but any translation into CN need only consider the result
of this process.

*MaySend*, *NoSend*, and *MustSend* constraints can be implement in CN if there
is a way to store a resource representing whether a message was sent on a port.
Then these constraints are just *ensures* clauses. *MaySend* will require
special handling.

GUMBO does not consider temporal logic.

## AGREE

AGREE's pure dataflow language can be simply translated to CN specs or just to C
code. Event ports already include whether an event is present at the port and so
a single dataflow model can be translated to a single relation between inputs
and outputs, with state variables present in both. This can be at the spec level
or further to the implementation.

Temporal properties are supported, called "real-time patterns". They have a syntax which forbids recursion but supports recurring events natively. AGREE's own tooling does not support reifying temporal properties, they are meant to be decomposed into per-component constraints which are similar to GUMBO in expressivity.

## FRET

FRET models have a fixed set of variables. Models with *at the next timepoint*
can be implemented like AGREE models, as functions of the variables implemented
as members of a struct. Similarly for *immediately* and *always*. *within X
ticks* requirements could be implemented by including a deadline for every such
requirement and a current tick variable, but implementing these specs may be
difficult. *eventually* and other temporal logic predicates are not
implementable.
