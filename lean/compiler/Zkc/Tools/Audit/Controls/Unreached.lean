module

/-! A control of the audit, in no library: the root of a library that does not import the module
under it (`Unreached.Apart`). Audited as a library, the file of that module is one that its root
does not import; audited as a library of tests, it is one that the audit's environment does not
have, since the audit loads this module alone. The audit must refuse both. -/
