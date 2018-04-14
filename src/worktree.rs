use std::mem;
use std::ptr;
use util::Binding;
use {raw, Buf, Error, Repository};

/// An external git worktree, i.e. one located out of the github repository
///
/// This structure corresponds to a `git_worktree` in libgit2.
///
/// When a repository goes out of scope it is freed in memory but not deleted
/// from the filesystem.
pub struct Worktree {
    raw: *mut raw::git_worktree,
}

impl Worktree {
    /// Create a Worktree from a Repository
    pub fn from_repo<'repo>(repo: &'repo Repository) -> Result<Self, Error> {
        let mut ret = ptr::null_mut();
        unsafe {
            try_call!(raw::git_worktree_open_from_repository(&mut ret, repo.raw()));
            Ok(Binding::from_raw(ret))
        }
    }

    /// Create a Repository from a Worktree
    pub fn to_repo(&self) -> Result<Repository, Error> {
        let mut ret = ptr::null_mut();
        unsafe {
            try_call!(raw::git_repository_open_from_worktree(&mut ret, self.raw));
            Ok(Binding::from_raw(ret))
        }
    }

    /// Ensure the worktree is well-formed.
    pub fn is_valid(&self) -> bool {
        unsafe { raw::git_worktree_validate(self.raw) == 0 }
    }

    /// Check if a worktree is locked
    ///
    /// Returns a tuple indicated lock status and the reason for locking, which
    /// may be empty
    pub fn is_locked(&self) -> Result<(bool, Buf), Error> {
        let buf = Buf::new();
        unsafe {
            let ret = try_call!(raw::git_worktree_is_locked(buf.raw(), self.raw));
            Ok((ret > 0, buf))
        }
    }

    /// Lock the given worktree, optionally with the given reason, if it is not already locked
    pub fn lock(&self, reason: Option<&str>) -> Result<(), Error> {
        let reason = try!(::opt_cstr(reason));
        unsafe {
            try_call!(raw::git_worktree_lock(self.raw, reason));
        }
        Ok(())
    }

    /// Unlock a worktree.
    ///
    /// If tree was successfully unlocked, returns `Ok(true)`.
    /// If the tree was already unlocked, returns `Ok(false)`.
    pub fn unlock(&self) -> Result<bool, Error> {
        unsafe {
            let ret = try_call!(raw::git_worktree_unlock(self.raw));
            Ok(ret == 0)
        }
    }

    /// Check if the work tree is prunable with the given options.
    ///
    /// A worktree is not prunable in the following scenarios:
    ///
    /// * the worktree is linking to a valid on-disk worktree. The
    ///   `valid` member will cause this check to be ignored.
    /// * the worktree is locked. The `locked` flag will cause this
    ///   check to be ignored.
    ///
    pub fn is_prunable(&self, opts: Option<&WorktreePruneOptions>) -> bool {
        let opts = match opts {
            None => ptr::null_mut(),
            Some(opts) => {
                let mut raw = unsafe{ opts.raw() };
                &mut raw as *mut _
            }
        };
        unsafe {
            raw::git_worktree_is_prunable(self.raw, opts) > 0
        }
    }

    /// Prune the working tree i.e. delete the git data structures on disk
    ///
    /// Only prunable working trees will be pruned, as determined by the
    /// WorktreePruneOptions flags
    pub fn prune(&self, opts: Option<&WorktreePruneOptions>) -> Result<(), Error> {
        let opts = match opts {
            None => ptr::null_mut(),
            Some(opts) => {
                let mut raw = unsafe{ opts.raw() };
                &mut raw as *mut _
            }
        };
        unsafe {
            try_call!(raw::git_worktree_prune(self.raw, opts));
        }
        Ok(())
    }
}

impl Drop for Worktree {
    fn drop(&mut self) {
        unsafe {
            raw::git_worktree_free(self.raw);
        }
    }
}

impl Binding for Worktree {
    type Raw = *mut raw::git_worktree;
    unsafe fn from_raw(ptr: *mut raw::git_worktree) -> Worktree {
        Worktree { raw: ptr }
    }
    fn raw(&self) -> *mut raw::git_worktree {
        self.raw
    }
}

/// Options which can be used to configure how a worktree is pruned
pub struct WorktreePruneOptions {
    flags: u32,
}

impl WorktreePruneOptions {
    /// Creates a default set of initialization options.
    ///
    /// By default, no flags are set.
    pub fn new() -> Self {
        WorktreePruneOptions { flags: 0 }
    }

    /// If true, prune working tree even if working tree is valid
    pub fn valid(&mut self, enabled: bool) -> &mut WorktreePruneOptions {
        self.flag(raw::GIT_WORKTREE_PRUNE_VALID, enabled)
    }

    /// If true, prune working tree even if it is locked
    pub fn locked(&mut self, enabled: bool) -> &mut WorktreePruneOptions {
        self.flag(raw::GIT_WORKTREE_PRUNE_LOCKED, enabled)
    }

    /// If prune, prune the checked out working tree
    pub fn working_tree(&mut self, enabled: bool) -> &mut WorktreePruneOptions {
        self.flag(raw::GIT_WORKTREE_PRUNE_WORKING_TREE, enabled)
    }

    fn flag(&mut self, flag: raw::git_worktree_prune_t, on: bool) -> &mut WorktreePruneOptions {
        if on {
            self.flags |= flag as u32;
        } else {
            self.flags &= !(flag as u32);
        }
        self
    }

    /// Creates a set of raw init options to be used with
    /// `git_worktree_prune_options`.
    ///
    /// This method is unsafe as the returned value may have pointers to the
    /// interior of this structure.
    pub unsafe fn raw(&self) -> raw::git_worktree_prune_options {
        let mut opts = mem::zeroed();
        assert_eq!(
            raw::git_worktree_prune_init_options(
                &mut opts,
                raw::GIT_WORKTREE_PRUNE_OPTIONS_VERSION
            ),
            0
        );
        opts.flags = self.flags;
        opts
    }
}

/// Options which can be used to configure how a worktree is initialized.
pub struct WorktreeAddOptions {}

impl WorktreeAddOptions {
    /// Creates a default set of initialization options.
    pub fn new() -> Self {
        WorktreeAddOptions {}
    }

    /// Creates a set of raw init options to be used as
    /// `git_worktree_add_options`.
    pub unsafe fn raw(&self) -> raw::git_worktree_add_options {
        let mut opts = mem::zeroed();
        assert_eq!(
            raw::git_worktree_add_init_options(&mut opts, raw::GIT_WORKTREE_ADD_OPTIONS_VERSION),
            0
        );
        opts
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::fs::remove_dir_all;
    use {raw, Repository, Worktree};

    fn worktree_init(repo: &Repository, mut path: PathBuf, name: &str) -> (PathBuf, Worktree) {
        path.push(name);
        let wt = repo.worktree(name, &path, None).unwrap();

        (path, wt)
    }

    #[test]
    fn from_repo() {
        let (td, repo) = ::test::repo_init();

        let (wt_path, _) = worktree_init(&repo, td.path().to_path_buf(), "wt1");

        // Opening the main repo as a worktree should fail
        assert!(Worktree::from_repo(&repo).is_err());

        let wt_repo = Repository::open(wt_path).unwrap();
        assert!(Worktree::from_repo(&wt_repo).is_ok());
    }


    #[test]
    fn is_valid() {
        // delete the main repository, shouldn't be valid
        {
            let (td, repo) = ::test::repo_init();

            let (_, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");
            assert!(wt.is_valid());

            assert!(td.close().is_ok());
            assert!(!wt.is_valid());
        }
        {
            let (td, repo) = ::test::repo_init();

            let (wt_path, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");
            assert!(wt.is_valid());

            assert!(remove_dir_all(&wt_path).is_ok());
            // still valid because the parent repo's worktree references are present
            assert!(wt.is_valid());
        }
    }

    #[test]
    fn lock() {
            // locking an unlocked worktree locks
            {
                let (td, repo) = ::test::repo_init();
                let (_, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");
                let (locked, reason) = wt.is_locked().unwrap();
                assert!(!locked);
                assert_eq!(reason.as_str().unwrap().len(), 0);

                assert!(wt.lock(Some("first lock")).is_ok());
                let (locked, reason) = wt.is_locked().unwrap();
                assert!(locked);
                assert_eq!(reason.as_str().unwrap(), "first lock");

                // and unlocking works too
                assert!(wt.unlock().unwrap());
                let (locked, reason) = wt.is_locked().unwrap();
                assert!(!locked);
                assert_eq!(reason.as_str().unwrap().len(), 0);
            }

            // lock w/ reason
            {
                let (td, repo) = ::test::repo_init();
                let (_, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");

                assert!(wt.lock(Some("first lock")).is_ok());
                let (locked, reason) = wt.is_locked().unwrap();
                assert!(locked);
                assert_eq!(reason.as_str().unwrap(), "first lock");

                // locking a locked worktree doesn't change reason
                assert!(wt.lock(Some("second lock")).is_err());
                let (locked, reason) = wt.is_locked().unwrap();
                assert!(locked);
                assert_eq!(reason.as_str().unwrap(), "first lock");
                assert!(wt.unlock().unwrap());
            }

            // lock w/o reason
            {
                let (td, repo) = ::test::repo_init();
                let (_, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");

                assert!(wt.lock(None).is_ok());
                let (locked, reason) = wt.is_locked().unwrap();
                assert!(locked);
                assert_eq!(reason.as_str().unwrap().len(), 0);
                assert!(wt.unlock().unwrap());
            }

            // unlock unlocked
            {
                let (td, repo) = ::test::repo_init();
                let (_, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");
                let (locked, _) = wt.is_locked().unwrap();
                assert!(!locked);

                assert!(wt.unlock().unwrap());
                let (locked, _) = wt.is_locked().unwrap();
                assert!(!locked);

            }
    }

    #[test]
    fn prune() {
        {
            let (td, repo) = ::test::repo_init();
            let (_, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");

            assert!(wt.prune(None).is_err());
            assert!(wt.to_repo().is_ok());
        }
        {
            let (td, repo) = ::test::repo_init();
            let (_, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");

            let mut opts = ::WorktreePruneOptions::new();
            opts.valid(true);
            assert!(wt.prune(Some(&opts)).is_ok());
            assert!(wt.to_repo().is_err());
        }
        {
            let (td, repo) = ::test::repo_init();
            let (_, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");
            assert!(wt.lock(None).is_ok());

            let mut opts = ::WorktreePruneOptions::new();
            opts.valid(true);
            assert!(wt.prune(Some(&opts)).is_err());
            assert!(wt.to_repo().is_ok());

            opts.locked(true);
            assert!(wt.prune(Some(&opts)).is_ok());
        }
        {
            let (td, repo) = ::test::repo_init();
            let (wt_path, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");

            let mut opts = ::WorktreePruneOptions::new();
            opts.valid(true);
            assert!(wt.prune(Some(&opts)).is_ok());
            assert!(wt.to_repo().is_err());
            assert!(wt_path.exists());
        }
        {
            let (td, repo) = ::test::repo_init();
            let (wt_path, wt) = worktree_init(&repo, td.path().to_path_buf(), "wt1");

            let mut opts = ::WorktreePruneOptions::new();
            opts.valid(true).working_tree(true);
            assert!(wt.prune(Some(&opts)).is_ok());
            assert!(wt.to_repo().is_err());
            assert!(!wt_path.exists());
            assert_eq!(repo.worktrees().unwrap().len(), 0);
        }
    }

    #[test]
    fn options() {
        macro_rules! t {
            ( $f: ident, $x: expr ) => {
                assert_eq!($f.flags, $x);
                unsafe {
                    let raw = $f.raw();
                    assert_eq!(raw.version, raw::GIT_WORKTREE_PRUNE_OPTIONS_VERSION);
                    assert_eq!(raw.flags, $x);
                }
            };
        }
        let mut opts = ::WorktreePruneOptions::new();
        assert_eq!(opts.flags, 0);

        opts.valid(true);
        t!(opts, raw::GIT_WORKTREE_PRUNE_VALID);
        opts.valid(false);
        t!(opts, 0);

        opts.locked(true);
        t!(opts, raw::GIT_WORKTREE_PRUNE_LOCKED);
        opts.locked(false);
        t!(opts, 0);

        opts.working_tree(true);
        t!(opts, raw::GIT_WORKTREE_PRUNE_WORKING_TREE);
        opts.working_tree(false);
        t!(opts, 0);

        opts.working_tree(true);
        opts.locked(true);
        t!(opts, raw::GIT_WORKTREE_PRUNE_WORKING_TREE|raw::GIT_WORKTREE_PRUNE_LOCKED);

        opts.valid(true);
        t!(opts, raw::GIT_WORKTREE_PRUNE_WORKING_TREE|raw::GIT_WORKTREE_PRUNE_LOCKED|raw::GIT_WORKTREE_PRUNE_VALID);

        opts.locked(false);
        assert_eq!(opts.flags, 5);
        t!(opts, 5);
        t!(opts, raw::GIT_WORKTREE_PRUNE_WORKING_TREE|raw::GIT_WORKTREE_PRUNE_VALID);
    }
}
