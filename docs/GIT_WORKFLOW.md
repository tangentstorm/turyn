# Git Workflow: Preserve History

This project should use an append-only commit workflow for optimization iterations.

## Required flow for each iteration

1. Sync with upstream history:
   - `git fetch --all --prune`
   - `git log --oneline --decorate --graph --all -n 30`
2. Create a new topic branch from the latest shared commit:
   - `git switch -c <new-branch-name>`
3. Make code changes and run checks.
4. Commit normally (no history rewriting):
   - `git add -A`
   - `git commit -m "<message>"`
5. Open PR from the topic branch.

## Do not do this

- Do **not** squash/reset local history before handing off changes.
- Do **not** force-push rewritten history for routine optimization updates.

## Notes

- If an upstream remote is not configured yet, add one before sync:
  - `git remote add upstream <repo-url>`
- If merge conflicts happen, resolve them in a new commit; do not replace prior commits.
