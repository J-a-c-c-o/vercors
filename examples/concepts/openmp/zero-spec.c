// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: case OpenMPzero
//:: suite puptol
//:: tools silicon
/*
 * Using a parallel for loop in OpenMP to blank an array.
 */
#include <omp.h>
#include <stdio.h>

/*@
  context \pointer(a, len, write);
  ensures   (\forall  int k;0 <= k && k < len ; a[k] == 0 );
@*/
void zero(int len, int a[]) {
  int i;
#pragma omp parallel for private(i)
  for (i = 0; i < len; i++)
  /*@
    context a != NULL;
    context Perm(a[i],1);
    ensures a[i] == 0;
  @*/
  {
    a[i] = 0;
  }
}
