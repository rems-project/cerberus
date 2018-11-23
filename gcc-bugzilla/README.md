# GCC Bugzilla

## Bug list 1

Taken from [this](https://gcc.gnu.org/bugzilla/buglist.cgi?bug_status=UNCONFIRMED&bug_status=NEW&bug_status=ASSIGNED&bug_status=SUSPENDED&bug_status=WAITING&bug_status=REOPENED&cf_known_to_fail_type=allwords&cf_known_to_work_type=allwords&component=c&order=changeddate%20DESC%2Ccomponent%20DESC%2Cbug_status%2Cpriority%2Cassigned_to%2Cbug_id&query_format=advanced) search.
Date: 20 Nov 2018

- 88088 - no example
- 84195 - about attributes
- 81432 - no example
- 88091 - regression test got the bug C++
- 46636 - about attributes
- 64918 - **bug in Cerberus**
- 63326 - about pragmas
- 87297 - errouneous warning message
- 53063 - something about .opt files
- 87806 - warning unused stuff
- 47781 - GNU extensions
- 88058 - **Cerberus detects the bug!**
- 44257 - GNU extension
- 61727 - pragma
- 85562 - about attributes
- 87964 - M Sebor copy and paste bug in GCC code
- 87975 - trigraphs
- 87998 - alias
- 87983 - warning wrong value in switch
- 87950 - warning
- 87944 - asm stuff
- 87924 - openACC
- 39438 - **Cerberus doesn't not have 'struct tm'**
- 66298 - indentation warning
- 79775 - warning message
- 87912 - pragma
- 87879 - warning
- 87890 - floats
- 47901 - warnings
- 78987 - warnings

### 88058 

```
88058.c:3:3: error: undefined behaviour: the operand of the unary '*' operator has an invalid value
  *a = 'x';
  ^~ 
```


## Bug list 2

Taken from [this](https://gcc.gnu.org/bugzilla/buglist.cgi?bug_status=UNCONFIRMED&bug_status=NEW&bug_status=ASSIGNED&bug_status=SUSPENDED&bug_status=WAITING&bug_status=REOPENED&cf_known_to_fail_type=allwords&cf_known_to_work_type=allwords&product=gcc&query_format=advanced&short_desc=Warning&short_desc_type=notregexp) search.
Date: 22 Nov 2018

- 67843: libstdc++
- 87514: share_ptr
- 88152: vectors
- 88149: templates
- 64132: libstdc++
- 85434: asm
- 53182: attributes
- 88165: objects
- 82918: optimisation
- 88158: c++ feature not supported by gcc
- 88144: remove obsolete syntax
- 86832: -fstack-protector-strong causes crash 
- 86828: fortran 
- 86735: fortran
- 28233: not ISO C
- 62009: convert pointer_map to hash_map
- 88076: coarray implementation
- 87957: lto struct error
- 87264: add a c++ optimisation
- 83545: **Cerberus detects UB**
- 87501: lto struct
- 88049: template
- 88164: constexpr
- 88162: template
- 88160: inline asm
- 88140: lto
- 79996: warning
- 85861: warning
- 80140: warning
- 81873: warning
- 69818: warning
- 85726: arithmetic optmisation
- 87485: int128
- 88143: fortran
- 85870: lto
- 78620: c++ initialisation
- 85548: c++ class initialisation
- 85644: stack protector
- 88139: fortran
- 88074: c++ complex and vector
- 84540: variadic template

### 82918

```c
struct array {
    int data[3];
};

void foo2(struct array* value, const struct array* value2) {
    if (&value == &value2) return;
    value->data[0] = value2->data[0];
    value->data[1] = value2->data[0];
    value->data[2] = value2->data[0];
}
```

This is not a bug, but an optmisation request in GCC. After the if, the GCC
can assume that `value` does not alias with `value2`.


### 86832

```c
static void a1(void *p) { }

int main(int argc, char **argv) {
    int i;
    a1(&i);
    return 0;
}
```

### 83545

ICE: Cerberus detects UB

```c
int a, b, c[1][25];

void f ()
{ 
  for (a = 0; a < 5; a++)
    for (b = 0; b < 5; b++)
      c[3970000000000000000][a * 5 + b] = 1;
}
```


## Bug list 3

Taken from [this](https://gcc.gnu.org/bugzilla/buglist.cgi?bug_status=UNCONFIRMED&bug_status=NEW&bug_status=ASSIGNED&bug_status=SUSPENDED&bug_status=WAITING&bug_status=REOPENED&cf_known_to_fail_type=allwords&cf_known_to_work_type=allwords&component=c&component=libgcc&component=middle-end&component=translation&query_format=advanced&short_desc=-W%2A&short_desc_type=notregexp) search.
Date: 23 Nov 2018

- 84191: c++ stuff
- 67222: ICE when calling posix_memalign
- 88097: missing optmisiation
- 88126: warning casting smaller ints
- 80793: Martin Sebor wants to clean the number of warnings
- 84292: libc function doesn't __sync_add_and_fetch not work
- 87593: not ISO C: custom formats
- 87649: pragma
- 87647: **Cerberus deems this constraint violation**
- 85879: fortran
- 71373: fortran
- 88085: vector alignment
- 71744: threads exceptions
- 67485: **Cerberus detects UB** when using the preprocessed file
- 60790: libatomic
- 58624: templates
- 88010: attributes
- 12849: arithmetic optmisation request (on the asm level)
- 87886: floats
- 19430: warning
- 77608: **Cerberus detects UB**, but it is trivial
- 65832: vector
- 87757: sprintf warning
- 71613: warning
- 87779: parser segfaults
- 50476: **Cerberus detects the UB**, but also trivial, they want to add warning
- 43728: warning
- 87775: builtin function stuff

## Bug list 4
Taken from [this](https://gcc.gnu.org/bugzilla/buglist.cgi?bug_status=UNCONFIRMED&bug_status=NEW&bug_status=ASSIGNED&bug_status=SUSPENDED&bug_status=WAITING&bug_status=REOPENED&cf_known_to_fail_type=allwords&cf_known_to_work_type=allwords&component=c&query_format=advanced&short_desc=-W%2A&short_desc_type=notregexp) search.
Date: 23 Nov 2018

- 23144: NOT ISO c
- 26154: openMP extension
- 81566: attribute allignment
- 82167: a program that segfaults GCC frontend, **it doesn't crash Cerberus**
- 77754: lto
- 86617: about volatile
- 87038: warning missing in a weird switch, **Cerberus does the correct thing**
- 87683: inline asm
- 87588: warning
- 82272: warning
- 87591: attributes
- 87578: not ISO: transparent union
- 87569: sizeof C++ references
- 86418: warning
- 52952: warning
- 81871: attribute


## Bug list 5
Looking at oldest C bugs.
Taken from [this](https://gcc.gnu.org/bugzilla/buglist.cgi?bug_status=UNCONFIRMED&bug_status=NEW&bug_status=ASSIGNED&bug_status=SUSPENDED&bug_status=WAITING&bug_status=REOPENED&cf_known_to_fail_type=allwords&cf_known_to_work_type=allwords&component=c&order=changeddate%2Ccomponent%20DESC%2Cbug_status%2Cpriority%2Cassigned_to%2Cbug_id&query_format=advanced) search.
Date: 23 Nov 2018

- 3481: attributes
- 8294: attributes
- 9071: warnings
- 16016: warnings
- 17170: warnings
- 18180: setjmp
- 20422: warnings
- 11813: cpp
- 18017: warnings
- 21438: warnings
- 28306: const/pure attributes
- 34941: warning ptrdiff_t size in printf, **Cerberus throws CV**
- 33823: bitfields