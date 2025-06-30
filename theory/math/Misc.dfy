
/**************************************************************************
  Miscelanious stuff
**************************************************************************/

module Misc {

  // apparently useless
  ghost function ite<T>(cond: bool, thenBranch: T, elseBranch: T) : T
  {
    if cond then thenBranch else elseBranch
  }

}