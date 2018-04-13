use std::ptr;
use std::mem;
use std::ffi::CString;
use {raw, Error, Repository};
use util::Binding;

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

    /// Ensure the working tree is well-formed.
    pub fn is_valid(&self) -> bool {
        unsafe { raw::git_worktree_validate(self.raw) == 0 }
    }

    /// Check if a working tree is locked
    pub fn is_locked(&self) -> bool {
        unsafe { raw::git_worktree_is_locked(ptr::null_mut(), self.raw) > 0 }
    }

    /// Lock the work tree, optionally with the given reason, if it is not already locked
    pub fn lock(&self, reason: Option<&str>) -> Result<(), Error> {
        let why = match reason {
            None => ptr::null(),
            Some(reason) => try!(CString::new(reason)).as_ptr(),
        };

        unsafe {
            try_call!(raw::git_worktree_lock(self.raw, why));
        }
        Ok(())
    }

    /// Unlock a worktree.
    ///
    /// If tree was successfully unlocked, returns Ok(true).
    /// If the tree was already unlocked, returns Ok(false).
    pub fn unlock(&self) -> Result<bool, Error> {
        let ret = unsafe { try_call!(raw::git_worktree_unlock(self.raw)) };
        Ok(ret == 0)
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
    pub fn is_prunable(&self, opts: &WorktreePruneOptions) -> bool {
        unsafe {
            let mut opts = opts.raw();
            raw::git_worktree_is_prunable(self.raw, &mut opts) > 0
        }
    }

    /// Prune the working tree i.e. delete the git data structures on disk
    ///
    /// Only prunable working trees will be pruned, as determined by the
    /// WorktreePruneOptions flags
    pub fn prune(&self, opts: &WorktreePruneOptions) -> Result<(), Error> {
        unsafe {
            let mut opts = opts.raw();
            try_call!(raw::git_worktree_prune(self.raw, &mut opts));
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

    /// Prune working tree even if working tree is valid
    pub fn valid(&mut self, enabled: bool) -> &mut WorktreePruneOptions {
        self.flag(raw::GIT_WORKTREE_PRUNE_VALID, enabled)
    }

    /// Prune working tree even if it is locked
    pub fn locked(&mut self, enabled: bool) -> &mut WorktreePruneOptions {
        self.flag(raw::GIT_WORKTREE_PRUNE_LOCKED, enabled)
    }

    /// Prune checked out working tree
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
            raw::git_worktree_prune_init_options(&mut opts, raw::GIT_WORKTREE_PRUNE_OPTIONS_VERSION),
            0
        );
        opts.flags = self.flags;
        opts
    }
}

/// Options which can be used to configure how a worktree is initialised
pub struct WorktreeInitOptions {}

impl WorktreeInitOptions {
    pub fn new() -> Self {
        WorktreeInitOptions {}
    }

    /// Creates a set of raw init options to be used with
    /// `git_worktree_add_options`.
    ///
    /// This method is unsafe as the returned value may have pointers to the
    /// interior of this structure.
    pub unsafe fn raw(&self) -> raw::git_worktree_add_options {
        let mut opts = mem::zeroed();
        assert_eq!(
            raw::git_worktree_add_init_options(&mut opts, raw::GIT_WORKTREE_ADD_OPTIONS_VERSION),
            0
        );
        opts
    }
}
