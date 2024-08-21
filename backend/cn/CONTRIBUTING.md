# Contributing guidelines

Learn how the CN project works and how you can contribute.

## Start here

TODO (dcm41): Setting up ocamlformat.
TOD (PS?): licensing agreements, acks etc?

We use [this GitHub project](https://github.com/orgs/GaloisInc/projects/23/views/9) to
track and coordinate development.

- All work starts by creating an issue.
- The issue is done when the work is done, tested, reviewed, and merged.

Read [contributing code](#contributing-code) for a step-by-step guide and an
explanation of why we do things this way.

Finally, read through these best practices guidelines.

- [Coding principles](#coding-principles)
- [Git guidelines](#git-guidelines)

Wondering if the juice is worth the squeeze? Jump to [Why this process?](#why-this-process)

## Setting up your development environment

We currently don't have any specific environment setup, but will add information
here as we progress in the project.

Mac OS X users should install the coreutils package with the following to run the `timeout` command which is used in test scripts (like `tests/run-cn.sh`).
```
brew install coreutils
```

## Contributing code

We are following [Trunk Based Development](https://trunkbaseddevelopment.com/)
methodology. Here's the development workflow.

1. [Create an issue](#create-an-issue)
1. [Fork the repo](#fork-the-repo)
1. [Write your code](#write-your-code)
1. [Create a PR and get it reviewed](#create-a-pr-and-get-it-reviewed)
1. [Merge your PR](#merge-your-pr)
1. [Delete your branch](#delete-your-branch)

### Create an issue

Create a GitHub issue describing the change you're planning to make.

- Assign it to yourself.
- Add a label for your organization (Galois, UCam, etc.)
- Add labels for the type of work (IDE, CN, documentation, etc.)

If you create the issue from the repo on GitHub, there are _bug_ and _feature_
issue templates to guide you through the process. Creating issues from the
project board unfortunately cannot use the templates.

Creating an issue automatically adds it to the project board, which helps us
track and prioritize ongoing work across different teams and organizations.
Tying issues to development work (and PRs) also makes it easier to answer questions
in the future, like "What went into the release we sent to the user study last
year?" or "What exactly did we fix from the red team's report?"

### Fork the repo

Fork the repo to make changes. This is standard practice for many projects (e.g. 
OCaml itself) and means contributors do not need write access to the repo.

**It is important to stay up-to-date with the original repository. 
Execute the following command at least daily:**
```
git pull --rebase upstream master
```

### Write your code

Here are some things to consider as you develop on your branch:

- Structure your changes into small commits that each address a specific task.
  See [What goes in a commit?](#what-goes-in-a-commit)

- Write unit and integration tests.

- Rebase regularly from upstream branch (`git pull -r upstream master`).

- Open a pull-request with your work (even in draft state). This runs CI tests.
  
- Push regularly to your remote branch. This backs-up your work.

When you're done...

### Create a PR and get it reviewed

When you are ready to have your changes reviewed, create a PR on GitHub.

- Summarize your change.
- Tag one or more reviewers.
- Link to the issue it addresses using `closes/resolves/fixes #XX`, where XX is the issue number.

The PR template will guide this process.

At least one reviewer needs to approve your PR. The _reviewer_ should either:

- **Request changes** for blocking/breaking issues and tricky fixes that require re-reviewing.
- **Approve** for suggestions/opinions that you trust the code author to consider and address as they see fit. Approving without comments or a simple _LGTM_ is acceptable.
- **Comment** for giving early feedback on a longer review.

For example, a reviewer marks a PR as _Approved_ even though they added a couple
of commments about the PR – the author can address (or ignore) them as they see
fit, and then merge without another round of reviewing.

Consider reflecting significant change requests or discussion points back into
the related issue(s) as appropriate.

### Merge your PR

Before merging, see [What goes in a commit?](#what-goes-in-a-commit) for
guidelines on merging your branch commit history into `main`.

## Coding principles

- Explicit is better than implicit
- Code should be written to be read, and not to make writing more convenient; assume that the person reading the code is you in a year
- Comments are critical, and should prioritize explaining why rather than what
- Similarly, good commit messages are required; good commit messages explain why a change was made (including links to issues where appropriate or reference to observed incorrect behaviors that may inform others who see similar failures) (more on this in [Git guidelines](#git-guidelines))
- Advanced development tools are great, but should not be required to develop a project
- Libraries should not call exit or produce console output (unless initiating a truly mandatory crash); libraries should not have fatal crashes
- Prefer library-first development (the functionality of any program should be available as a library)
- A clean version control history is important (e.g., to support bisecting and code understanding), but extensive history rewriting is not important (more on this in [Git guidelines](#git-guidelines))

## Git guidelines

- [General guidelines](#general-guidelines)
- [What goes in a commit?](#what-goes-in-a-commit)
- [Why support `git bisect`?](#why-support-git-bisect)

### General guidelines

- Do not commit directly to `main`.

- Do not merge WIP commits that break the build (required for
  [`git bisect`](#why-support-git-bisect)).

- Write short, useful commit messages with a consistent style (see [What goes in
  a commit?](#what-goes-in-a-commit)).

- Keep your topic branches small to facilitate review.

- Before merging someone else's PR, make sure other reviewers'
  comments are resolved, and that the MP author considers the PR ready
  to merge.

- Use `git pull --rebase # or -r` to fetch remote changes. This will rebase local
  changes on top of remote changes, which keeps history more linear and will keep
  local changes instead of discarding them in the case that someone force pushed
  to the remote.

- Avoid `git push --force` to shared branches. If you must, prefer `git push
--force-with-lease --force-if-includes`. See [The Dark Side of the Force Push][]
  and [--force considered harmful; understanding git's --force-with-lease][].

- [Optional] Configure Git so that your commits are [signed][].

[The Dark Side of the Force Push]: http://willi.am/blog/2014/08/12/the-dark-side-of-the-force-push/
[--force considered harmful; understanding git's --force-with-lease]: https://developer.atlassian.com/blog/2015/04/force-with-lease/
[seven rules]: https://chris.beams.io/posts/git-commit/#seven-rules
[signed]: https://git-scm.com/book/en/v2/Git-Tools-Signing-Your-Work

### What goes in a commit?

Follow these [seven rules][] for writing commit messages.

Commits should be minimal self-contained changes, reflected in the commit
message. This is an art we aspire to. See [this
article](https://confluence.galois.com/pages/viewpage.action?pageId=82346420)
for an in-depth discussion.

For example, consider these sets of commit messages.

- `Add logging util to capture timing`
- `Add new core algorithm, disabled by default`
- `Add flag to use new core algorithm`

is preferable to

- `Add new core algorithm with flag to enable`

is preferable to

- `First attempt at core algorithm`
- `Fix logging`
- `Refactor logging fix`
- `Fix up algorithm`
- `WIP`
- `Finish alg`
- `Add flag`

Small commits that each address a single, self-contained issue are easy to review, easy to trace in `git log`, and make `git bisect` much more effective.

### Why support `git bisect`?

`git bisect <known-good-commit> <known-bad-commit>` is a debugging utility to find which commit first introduced a bug. Using a binary search, it will iteratively check out a commit between a known-good and known-bad commit; you will then run tests to determine if the bug is present and mark the commit "good" or "bad". Eventually, it will point you to the first bad commit.

This only works if every commit is well formed. Suppose you have an example that triggers a bug, and you use `git bisect` to build and test each commit on that example. Consider the following series of commits.

1. `Partially implements XX (broken)`
2. `Finishes implementing XX (fixed)`

When `git bisect` checks out (1), you will be unable to build the project or determine if the bug is present.

The guidelines in [What goes in a commit?](#what-goes-in-a-commit) support `git bisect` by encouraging each commit to be small and self contained.

## Why this process?

We are coordinating development across a variety of teams at different organizations around the world, and the project is expected to run for several years. Despite the long duration, our timeline is tight. Hence, we need to balance several concerns:

- **Visibility**. We need to understand what work has been planned, started, completed, or blocked, and who is doing it, in order to prioritize our next steps as things slip or circumstances change. We use issues and the project board for this.

- **Traceability**. When code changes, we need to understand why. This sometimes
  lives in commit messages, PR messages, issues, or a developer's head. In this
  project, we're standardizing on issues, which is why all work starts with an
  issue. Commit messages still give context for specific changes (details
  [here](#what-goes-in-a-commit)); multiple commits may support a single issue.

- **Development best practices.** Software engineering research and personal experience both suggest that coherent contribution guidelines ease development while raising the level of assurance. See [here](https://gitlab-ext.galois.com/program-analysis/guidance/-/blob/78d2d6229f027579384c39a76cf28026b03279a7/BestPractices.org) for motivation and details of specific best practices, some of which are adopted in this document.

- **Developer ergonomics**. Development should focus on building neat stuff, not fighting a process. We don't want to add boilerplate for no reason.
