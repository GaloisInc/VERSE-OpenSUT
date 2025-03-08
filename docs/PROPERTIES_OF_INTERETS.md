# Properties of interest

Based on discussions with our DIB partners, highlighting their current pain points as well as our past experience with assurance of complex systems, we arrived at the following properties of interest. For each property, we highlight how we address it for OpenSUT.

- [Properties of interest](#properties-of-interest)
  - ["Classical" Correctness Properties](#classical-correctness-properties)
  - [State Machine Encoding](#state-machine-encoding)
  - [Functional correctness](#functional-correctness)
  - [Information flow properties](#information-flow-properties)
  - [Interfacing with a Memory Safe Language (MSL)](#interfacing-with-a-memory-safe-language-msl)
  - [Time and Resource Separation Properties](#time-and-resource-separation-properties)


## "Classical" Correctness Properties

Read as: **no undefined behavior (UB)** and **memory safety**. Undefined behavior means:

* signed integer over and underflow
* use of an uninitialized variable
* oversized shift amount
* out of bounds array access
* null pointer dereferencing

Generally we don't want any undefined behavior in the code, 
as it leads to security errors and functional errors[^1] [^2]. Even in 2025, the undefined behavior is responsible for 5 out of [Top 25 CWEs](https://cwe.mitre.org/top25/archive/2024/2024_cwe_top25.html).

Memory safety is essential for ensuring a secure code, and is tied to the absence of UB. However, the mere absence of UB does not guarantee memory safety, as memory can still be mis-managed by incorrect code. Most CWEs are still tied to memory safety[^3], and there is significant momentum in moving towards memory safe languages for future systems[^4] [^5], and for retrofitting of existing systems[^6]. Furthermore, there is emerging evidence that even if only new code is memory safe, it increases the overall security of the system[^7].

VERSE tooling is [very suitable for mitigating UB in C code](https://www.cl.cam.ac.uk/~pes20/cerberus/), and CN verified code is guaranteed to contain only defined behavior. 

<!-- Guide to UB -->
[^1]: https://blog.regehr.org/archives/213

<!-- What everyone should know about UB -->
[^2]: https://blog.llvm.org/2011/05/what-every-c-programmer-should-know.html

<!-- CISA The Case for Memory Safe Roadmap -->
[^3]: https://www.cisa.gov/case-memory-safe-roadmaps

<!-- Fact Sheet: memory safety -->
[^4]: https://bidenwhitehouse.archives.gov/oncd/briefing-room/2024/02/26/memory-safety-fact-sheet/

<!-- CSET: Memory safety explainer -->
[^5]: https://cset.georgetown.edu/article/memory-safety-an-explainer/

<!-- TRACTOR announcement -->
[^6]: https://www.darpa.mil/news-events/2024-07-31a

<!-- Eliminating Memory Safety Vulnerabilities at the Source  -->
[^7]: https://security.googleblog.com/2024/09/eliminating-memory-safety-vulnerabilities-Android.html?m=1


Covered properties from **Focusing PROVERS Program Metrics Appendix A**: 
* Memory safety
* Undefined behavior
* Structural data properties


## State Machine Encoding

This property ensures that my code follows the correct usage pattern. This is because incorrect API calls lead to security issues, especially in cryptographic algorithms, as well as functional issues, by entering unreachable/undefined states.

Note that the state machines are derived from the requirements and the system model, or from usage constraints of specific algorithms. VERSE tooling can verify that the code implements the state machine, assuming the state machine is correct to start with, and has been verified with model checkers, such as [SRI-SAL](https://sal.csl.sri.com/). 

Covered properties from **Focusing PROVERS Program Metrics Appendix A**: 
* State Machine Adherence
* API Usage Patterns

## Functional correctness

Builds on top of Classical Correctness properties (no UB/memory safety), and ensures my code is doing what is supposed to and nothing else, which is especially important for certification and safety and security critical applications. VERSE tooling is well suited to prove functional correctness of C code, and we provide multiple examples in the OpenSUT.

Covered properties from **Focusing PROVERS Program Metrics Appendix A**: 
* Functional correctness

## Information flow properties

In various applications we have *low* and *high* data, show that *low* is not influenced by *high* (can be generalized to multiple levels of security). We want to show correct handling and separation of data (no unintentional data leaks), which is needed to prove separation properties.

This can be achieved with a notion of *Security levels*, re-use the approach taken by [JML](https://en.wikipedia.org/wiki/Java_Modeling_Language). Technically, a security level is a set of heap locations and a declassification is part of the method contract. [Chapter 13](https://formal.iti.kit.edu/biblio/projects/key/chapter13.pdf) from the [Deductive SW verification book](https://www.key-project.org/thebook2/) provides more details. [The Key Project](https://www.key-project.org/) checks JML specifications, and includes a [symbolic debugger](https://www.key-project.org/applications/debugging/) as an Eclipse plugin ([video](https://www.youtube.com/watch?v=xvKGVyU92MY&t=2s)). More information can be found in this lecture: [Deductive Verification of Information Flow Properties of Java Programs](https://formal.kastel.kit.edu/~beckert/teaching/AnwendungFormalerVerifikation2011/08_KeY_information_flow.pdf)

An alternate approach is taken in SPARK/Ada - annotate which variable the output depends on [[blog post](https://blog.adacore.com/spark-2014-rationale-information-flow)]

VERSE tooling currently does not support reasoning about information flow properties, but the JML-like approach outlined above seems feasible. Please note that code level reasoning about information flow needs to be connected with system-level reasoning using for example AADL tools (see the [CASE AADL tutorial](https://github.com/GaloisInc/CASE-AADL-Tutorial/tree/ee0947b07eaa308c8bb6ac10c010b7e089803d65/aadl_book/chapter1_aadl_basics#specifying-data-flow) for details).

Covered properties from **Focusing PROVERS Program Metrics Appendix A**: 
* Data-ﬂow restrictions


## Interfacing with a Memory Safe Language (MSL)

Even though new code will be written in MSL[^6], lot of legacy code cannot be translated (for various reasons)[^7]. Verification of the non-MSL interfaces would increase your MSL-like codebase for certification.

We want to expand the memory safety from MSL to C code by ensuring safety of the interfaces, e.g., *Rust FFI => pass a data structure => C library API & ownership properties => return a modified data structure*, which in turn changes unsafe FFI calls to safe FFI calls.

VERSE tooling is well suited for the reasoning about interfaces, but further experimentation is needed to connect C verification tools (such as CN) and Rust verification tools (such as [Verus](https://github.com/verus-lang/verus)).

## Time and Resource Separation Properties

This class of properties is important for a multi-core CPU, which is becoming more prevalent in modern aerospace applications. We want to show that a given application cannot influence or be influenced by another application running on the CPU. E.g., we would like to know if the inter-component data flow queue management algorithms behave correctly even when resources are exhausted (e.g., a queue is full, a free buffer is not available).

Proving these properties is needed to support [CAST-32A](https://www.cast32a.com/) and modern mission computers and fast re-certification. 
Proving these properties needs to be tackled at multiple levels, starting from a system model and going all the way to source code and binary code. This is achieved with multiple tools, and will likely include assumptions about the underlying hardware. 

Resource analysis can be done statically with [AADL CAMET tools](https://tools.galois.com/camet), for the dynamic resource allocation and behavior, we would like to know if the flow management/queue management algorithms behave correctly even when resources are exhausted (e.g. a queue is full, a free buffer is not available) . 
Information Flow Analysis is necessary, and can be likely achieved with the VERSE tools, as mentioned in the [Information flow properties](#information-flow-properties) sections. However, a a full separation proof is very likely out of scope for VERSE tooling.

Covered properties from **Focusing PROVERS Program Metrics Appendix A**: 
* Execution time
* Resource Limitation
