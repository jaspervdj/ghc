/* -----------------------------------------------------------------------------
 * $Id: Rts.h,v 1.9 1999/11/09 15:47:08 simonmar Exp $
 *
 * (c) The GHC Team, 1998-1999
 *
 * Top-level include file for the RTS itself
 *
 * ---------------------------------------------------------------------------*/

#ifndef RTS_H
#define RTS_H

#ifndef IN_STG_CODE
#define IN_STG_CODE 0
#endif
#include "Stg.h"

/* -----------------------------------------------------------------------------
   Miscellaneous garbage
   -------------------------------------------------------------------------- */

#if ! defined(EXIT_SUCCESS) || ! defined(EXIT_FAILURE)
/* "stdlib.h" should have defined these; but at least
   on SunOS 4.1.3, this is not so.
*/
#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1
#endif

/* declarations for runtime flags/values */
#define MAX_RTS_ARGS 32

/* -----------------------------------------------------------------------------
   Useful typedefs
   -------------------------------------------------------------------------- */

typedef unsigned int  nat;           /* at least 32 bits (like int) */
typedef unsigned long lnat;          /* at least 32 bits            */
typedef unsigned long long ullong;   /* at least 32 bits            */
  
typedef enum { 
    rtsFalse = 0, 
    rtsTrue 
} rtsBool;

/* -----------------------------------------------------------------------------
   Assertions and Debuggery
   -------------------------------------------------------------------------- */

#ifndef DEBUG
#define IF_DEBUG(c,s)  doNothing()
#else
#define IF_DEBUG(c,s)  if (RtsFlags.DebugFlags.c) { s; }
#endif

/* -----------------------------------------------------------------------------
   Attributes
   -------------------------------------------------------------------------- */

#ifdef __GNUC__     /* Avoid spurious warnings                             */
#if __GNUC__ >= 2 && __GNUC_MINOR__ >= 7
#define STG_NORETURN  __attribute__ ((noreturn))
#define STG_UNUSED    __attribute__ ((unused))
#else
#define STG_NORETURN  
#define STG_UNUSED
#endif
#else
#define STG_NORETURN  
#define STG_UNUSED
#endif

/* -----------------------------------------------------------------------------
   Useful macros and inline functions
   -------------------------------------------------------------------------- */

/* 
 * Use this on the RHS of macros which expand to nothing
 * to make sure that the macro can be used in a context which
 * demands a non-empty statement.
 */

#define doNothing() do { } while (0)

#define stg_min(a,b) ({typeof(a) _a = (a), _b = (b); _a <= _b ? _a : _b; })
#define stg_max(a,b) ({typeof(a) _a = (a), _b = (b); _a <= _b ? _b : _a; })

#endif RTS_H
