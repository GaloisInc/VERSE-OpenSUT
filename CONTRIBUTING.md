# Contributing guidelines

- [Contributing guidelines](#contributing-guidelines)
  - [Coding standards](#coding-standards)
  - [Version control](#version-control)
  - [Git guidelines](#git-guidelines)


## Coding standards

We intend to use a properly configured linter for each supported language. Run a linter before committing your code. Some general coding principles we want to adhere to (inspired by [Tristan's coding standards Confluence page](https://confluence.galois.com/display/~tristan/Haskell+Coding+Standards)):

* Explicit is better than implicit
* Code should be written to be read, and not to make writing more convenient; assume that the person reading the code is you in a year
* Comments are critical, and should prioritize explaining why rather than what
* Similarly, good commit messages are required; good commit messages explain why a change was made (including links to issues where appropriate or reference to observed incorrect behaviors that may inform others who see similar failures) (more on this in [Git guidelines](#git-guidelines))
* Strive to make error states unrepresentable (but not at the expense of clarity)
* Advanced development tools are great, but should not be required to develop a project
* Libraries should not call exit or produce console output (unless initiating a truly mandatory crash); libraries should not have fatal crashes
* Prefer library-first development (the functionality of any program should be available as a library)
* A clean version control history is important (e.g., to support bisecting and code understanding), but extensive history rewriting is not important (more on this in [Git guidelines](#git-guidelines))

VERSE project specific guidelines:
* Use *snake_case* when possible for naming files and folders. The only exceptions exist:
  * the top-level files, such as `README.md`, `CONTRIBUTING` and such.
  * `Dockerfile*` is capitalized, per Docker [naming conventions](https://stackoverflow.com/a/63995752)
  * `Makefile*` is capitalized, per GNU Make [naming conventions](https://www.gnu.org/software/make/manual/make.html#Makefile-Names)
* Include [submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) at the point of use (e.g. `./foo/bar/my_submodule`), rather than in the root directory (`./my_submodule`).

## Version control

The VERSE project uses Git for revision control. Currently, we are
using [Github][] for hosting and code review.

The VERSE project and its client does not demand that commits or MRs
are cryptographically signed.  You are welcome to setup signatures and
follow a workflow that preserves signatures if you wish, but it is not
mandatory.

We are following [Trunk Based Development](https://trunkbaseddevelopment.com/) (TBD) methodology.
The development workflow is as follows:

1. In the Github project repository, create an issue describing the change
   you're planning to make.
2. Push "Create a branch" in the newly created issue.
   Github will create a topic branch named `XX-issue-name` where `XX` is the issue number.

   Checkout the branch
    and a Pull Request (PR), all linked to the
   issue. Make sure that the PR is marked as draft, untilizing `DRAFT` prefix.
   You can perform these steps manually but Github makes it easier.
3. Locally, in a terminal opened in the project repo clone, pull updates
   from the remote and switch to the branch created in step #2.
   Or use IDE of your choice to accomplish the same.
4. Develop and test the change locally. If applicable, make sure to add
   unit and integration tests for the change.  Push your commits frequently.
   Once you have some commits in your branch, go to the Github project repository,
   and open a new *DRAFT* pull request. If not done automatically, in the PR description
   link to the issue it is closing using `closes/resolves/fixes` [keyword](https://docs.github.com/en/issues/tracking-your-work-with-issues/linking-a-pull-request-to-an-issue)
5. If you are working with another developer on
   the same topic branch, use `git pull --rebase` to rebase your local
   branch against the remote topic branch (resolving any conflicts
   that arise) before pushing, which will keep history clean on the
   topic branch. A few notes:
   * avoid merge conflicts as much as possible, as they are difficult to resolve. Communicate your intent to your colleagues ahead of time, and limit the scope of your changes as much as possible
   * if a merge conflict arises (e.g. against the `main` branch), and is non-trivial to resolve, contact the author of the changes and work together to ensure a proper resolve
6. Push changes to the remote origin. This will trigger CI pipeline execution.
   If the tests pass and you're done (i.e. the PR fully addresses the issue it is linked to), mark the PR as *READY FOR REVIEW*
7. Typically, at least one _other_ person must review any changes to
   the parent branch, and approve it using the Github PR interface. A
   _reviewer_ should check that all necessary comments are addressed. The _reviewer_ should either:
   * **Request changes** for blocking/breaking issues and tricky fixes that require re-reviewing
   * **Approve** for suggestions/opinions that you trust the code author to consider and address as they see fit. Approving without comments or only a simple *LGTM* is acceptable
   * **Comment** for giving early feedback on a longer review
   * For example, a reviewer marks a PR as *Approved* even though they added a couple of commments about the PR – the author can address it if they agree, but the PR can be merged as is
8. If a reviewer deems some comments must be addressed, please ensure
   that discussions salient to the changes are captured in the merge
   request and in the associated issues.
9.  Note that *force-pushes are dangerous*, so make sure that you
   know that no one else has pushed changes to the branch that are not
   in the history of your local branch.  If others on the team are
   pulling and testing it locally, they will need to fix up their
   local branches with `git checkout <yourbranch>`, `git fetch`, and
   `git reset --hard origin/<yourbranch>`. For more details, please
   see [The Dark Side of the Force Push][] and [--force considered
   harmful; understanding git's --force-with-lease][].
10. Once it has been approved, PR author merges the PR (in Github push the `Merge pull request`
   button in the PR UI). Github will execute
   CI/CD pipeline and complete the merge.
11. If, for some reason the source branch was not automatically deleted, the reviewer that merges the branch should manually delete
   the branch after the merge.
12. Do not forget to occasionally clean up local branches that have
    been merged!  Doing so on a weekly cadence means that you do not
    become overwhelmed with branches.

[The Dark Side of the Force Push]: http://willi.am/blog/2014/08/12/the-dark-side-of-the-force-push/
[--force considered harmful; understanding git's --force-with-lease]: https://developer.atlassian.com/blog/2015/04/force-with-lease/
[Magit]: https://magit.vc/
[GitKraken]: https://www.gitkraken.com/
[Github]: https://github.com/

## Git guidelines

- Do not commit directly to `main`.
- To support bisecting, do not merge WIP commits that break the build.
  On topic branches, squash commits as needed before merging, but only
  to reduce excessive small commits; the development history of topic
  branches should be preserved as much as is reasonable. Use your
  best judgement. Ask a git expert for advise if you are stuck more
  than 10 minutes.
- Write short, useful commit messages with a consistent style. Follow
  these [seven rules][], with the amendment that on this project, we
  have adopted the convention of ending the subject line with a
  period. Galois has excellent resources about commit messages, please consult
  [What goes into a commit](https://confluence.galois.com/pages/viewpage.action?pageId=82346420)
- Keep your topic branches small to facilitate review.
- Before merging someone else's PR, make sure other reviewers'
  comments are resolved, and that the MP author considers the PR ready
  to merge.
- For security-sensitive code, ensure your changes have received an
  in-depth review, preferably from multiple reviewers. Please consult [Code reviews page](https://confluence.galois.com/display/EN/Code+Reviews) for more details.
- Configure Git so that your commits are [signed][].
- Whenever possible, use automation to avoid committing errors or
  noise (e.g., extraneous whitespace).  Use linters, automatic code
  formatters, test runners, and other static analysis tools.
  Configure your editor to use them, and when feasible, integrate them
  into the upstream continuous integration checks.

[seven rules]: https://chris.beams.io/posts/git-commit/#seven-rules
[signed]: https://git-scm.com/book/en/v2/Git-Tools-Signing-Your-Work
