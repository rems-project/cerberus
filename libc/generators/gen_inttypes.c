#include<stdio.h>
#include<inttypes.h>

// Generate an inttypes.h file

int main(void) {
  printf("#include <stdint.h>\n"
         "// TODO: move this in Ail (for now we are making a implementation choice)\n"
         "typedef struct {\n"
         "  intmax_t quot;\n"
         "  intmax_t rem;\n"
         "} imaxdiv_t;\n\n\n");
  
  printf("// TODO: move them somehow in Ail (for now we are making a implementation choice)\n");
  printf("#define PRId8 \"%s\"\n", PRId8);
  printf("#define PRId16 \"%s\"\n", PRId16);
  printf("#define PRId32 \"%s\"\n", PRId32);
  printf("#define PRId64 \"%s\"\n", PRId64);

  printf("#define PRIdLEAST8 \"%s\"\n", PRIdLEAST8);
  printf("#define PRIdLEAST16 \"%s\"\n", PRIdLEAST16);
  printf("#define PRIdLEAST32 \"%s\"\n", PRIdLEAST32);
  printf("#define PRIdLEAST64 \"%s\"\n", PRIdLEAST64);

  printf("#define PRIdFAST8 \"%s\"\n", PRIdFAST8);
  printf("#define PRIdFAST16 \"%s\"\n", PRIdFAST16);
  printf("#define PRIdFAST32 \"%s\"\n", PRIdFAST32);
  printf("#define PRIdFAST64 \"%s\"\n", PRIdFAST64);

  printf("#define PRIdMAX \"%s\"\n", PRIdMAX);

  printf("#define PRIdPTR \"%s\"\n", PRIdPTR);

  printf("#define PRIi8 \"%s\"\n", PRIi8);
  printf("#define PRIi16 \"%s\"\n", PRIi16);
  printf("#define PRIi32 \"%s\"\n", PRIi32);
  printf("#define PRIi64 \"%s\"\n", PRIi64);

  printf("#define PRIiLEAST8 \"%s\"\n", PRIiLEAST8);
  printf("#define PRIiLEAST16 \"%s\"\n", PRIiLEAST16);
  printf("#define PRIiLEAST32 \"%s\"\n", PRIiLEAST32);
  printf("#define PRIiLEAST64 \"%s\"\n", PRIiLEAST64);

  printf("#define PRIiFAST8 \"%s\"\n", PRIiFAST8);
  printf("#define PRIiFAST16 \"%s\"\n", PRIiFAST16);
  printf("#define PRIiFAST32 \"%s\"\n", PRIiFAST32);
  printf("#define PRIiFAST64 \"%s\"\n", PRIiFAST64);

  printf("#define PRIiMAX \"%s\"\n", PRIiMAX);

  printf("#define PRIiPTR \"%s\"\n", PRIiPTR);

  printf("#define PRIo8 \"%s\"\n", PRIo8);
  printf("#define PRIo16 \"%s\"\n", PRIo16);
  printf("#define PRIo32 \"%s\"\n", PRIo32);
  printf("#define PRIo64 \"%s\"\n", PRIo64);

  printf("#define PRIoLEAST8 \"%s\"\n", PRIoLEAST8);
  printf("#define PRIoLEAST16 \"%s\"\n", PRIoLEAST16);
  printf("#define PRIoLEAST32 \"%s\"\n", PRIoLEAST32);
  printf("#define PRIoLEAST64 \"%s\"\n", PRIoLEAST64);

  printf("#define PRIoFAST8 \"%s\"\n", PRIoFAST8);
  printf("#define PRIoFAST16 \"%s\"\n", PRIoFAST16);
  printf("#define PRIoFAST32 \"%s\"\n", PRIoFAST32);
  printf("#define PRIoFAST64 \"%s\"\n", PRIoFAST64);

  printf("#define PRIoMAX \"%s\"\n", PRIoMAX);

  printf("#define PRIoPTR \"%s\"\n", PRIoPTR);

  printf("#define PRIu8 \"%s\"\n", PRIu8);
  printf("#define PRIu16 \"%s\"\n", PRIu16);
  printf("#define PRIu32 \"%s\"\n", PRIu32);
  printf("#define PRIu64 \"%s\"\n", PRIu64);

  printf("#define PRIuLEAST8 \"%s\"\n", PRIuLEAST8);
  printf("#define PRIuLEAST16 \"%s\"\n", PRIuLEAST16);
  printf("#define PRIuLEAST32 \"%s\"\n", PRIuLEAST32);
  printf("#define PRIuLEAST64 \"%s\"\n", PRIuLEAST64);

  printf("#define PRIuFAST8 \"%s\"\n", PRIuFAST8);
  printf("#define PRIuFAST16 \"%s\"\n", PRIuFAST16);
  printf("#define PRIuFAST32 \"%s\"\n", PRIuFAST32);
  printf("#define PRIuFAST64 \"%s\"\n", PRIuFAST64);

  printf("#define PRIuMAX \"%s\"\n", PRIuMAX);

  printf("#define PRIuPTR \"%s\"\n", PRIuPTR);

  printf("#define PRIx8 \"%s\"\n", PRIx8);
  printf("#define PRIx16 \"%s\"\n", PRIx16);
  printf("#define PRIx32 \"%s\"\n", PRIx32);
  printf("#define PRIx64 \"%s\"\n", PRIx64);

  printf("#define PRIxLEAST8 \"%s\"\n", PRIxLEAST8);
  printf("#define PRIxLEAST16 \"%s\"\n", PRIxLEAST16);
  printf("#define PRIxLEAST32 \"%s\"\n", PRIxLEAST32);
  printf("#define PRIxLEAST64 \"%s\"\n", PRIxLEAST64);

  printf("#define PRIxFAST8 \"%s\"\n", PRIxFAST8);
  printf("#define PRIxFAST16 \"%s\"\n", PRIxFAST16);
  printf("#define PRIxFAST32 \"%s\"\n", PRIxFAST32);
  printf("#define PRIxFAST64 \"%s\"\n", PRIxFAST64);

  printf("#define PRIxMAX \"%s\"\n", PRIxMAX);

  printf("#define PRIxPTR \"%s\"\n", PRIxPTR);

  printf("#define PRIX8 \"%s\"\n", PRIX8);
  printf("#define PRIX16 \"%s\"\n", PRIX16);
  printf("#define PRIX32 \"%s\"\n", PRIX32);
  printf("#define PRIX64 \"%s\"\n", PRIX64);

  printf("#define PRIXLEAST8 \"%s\"\n", PRIXLEAST8);
  printf("#define PRIXLEAST16 \"%s\"\n", PRIXLEAST16);
  printf("#define PRIXLEAST32 \"%s\"\n", PRIXLEAST32);
  printf("#define PRIXLEAST64 \"%s\"\n", PRIXLEAST64);

  printf("#define PRIXFAST8 \"%s\"\n", PRIXFAST8);
  printf("#define PRIXFAST16 \"%s\"\n", PRIXFAST16);
  printf("#define PRIXFAST32 \"%s\"\n", PRIXFAST32);
  printf("#define PRIXFAST64 \"%s\"\n", PRIXFAST64);

  printf("#define PRIXMAX \"%s\"\n", PRIXMAX);

  printf("#define PRIXPTR \"%s\"\n", PRIXPTR);
  printf("#define SCNd8 \"%s\"\n", SCNd8);
  printf("#define SCNd16 \"%s\"\n", SCNd16);
  printf("#define SCNd32 \"%s\"\n", SCNd32);
  printf("#define SCNd64 \"%s\"\n", SCNd64);

  printf("#define SCNdLEAST8 \"%s\"\n", SCNdLEAST8);
  printf("#define SCNdLEAST16 \"%s\"\n", SCNdLEAST16);
  printf("#define SCNdLEAST32 \"%s\"\n", SCNdLEAST32);
  printf("#define SCNdLEAST64 \"%s\"\n", SCNdLEAST64);

  printf("#define SCNdFAST8 \"%s\"\n", SCNdFAST8);
  printf("#define SCNdFAST16 \"%s\"\n", SCNdFAST16);
  printf("#define SCNdFAST32 \"%s\"\n", SCNdFAST32);
  printf("#define SCNdFAST64 \"%s\"\n", SCNdFAST64);

  printf("#define SCNdMAX \"%s\"\n", SCNdMAX);

  printf("#define SCNdPTR \"%s\"\n", SCNdPTR);

  printf("#define SCNi8 \"%s\"\n", SCNi8);
  printf("#define SCNi16 \"%s\"\n", SCNi16);
  printf("#define SCNi32 \"%s\"\n", SCNi32);
  printf("#define SCNi64 \"%s\"\n", SCNi64);

  printf("#define SCNiLEAST8 \"%s\"\n", SCNiLEAST8);
  printf("#define SCNiLEAST16 \"%s\"\n", SCNiLEAST16);
  printf("#define SCNiLEAST32 \"%s\"\n", SCNiLEAST32);
  printf("#define SCNiLEAST64 \"%s\"\n", SCNiLEAST64);

  printf("#define SCNiFAST8 \"%s\"\n", SCNiFAST8);
  printf("#define SCNiFAST16 \"%s\"\n", SCNiFAST16);
  printf("#define SCNiFAST32 \"%s\"\n", SCNiFAST32);
  printf("#define SCNiFAST64 \"%s\"\n", SCNiFAST64);

  printf("#define SCNiMAX \"%s\"\n", SCNiMAX);

  printf("#define SCNiPTR \"%s\"\n", SCNiPTR);

  printf("#define SCNo8 \"%s\"\n", SCNo8);
  printf("#define SCNo16 \"%s\"\n", SCNo16);
  printf("#define SCNo32 \"%s\"\n", SCNo32);
  printf("#define SCNo64 \"%s\"\n", SCNo64);

  printf("#define SCNoLEAST8 \"%s\"\n", SCNoLEAST8);
  printf("#define SCNoLEAST16 \"%s\"\n", SCNoLEAST16);
  printf("#define SCNoLEAST32 \"%s\"\n", SCNoLEAST32);
  printf("#define SCNoLEAST64 \"%s\"\n", SCNoLEAST64);

  printf("#define SCNoFAST8 \"%s\"\n", SCNoFAST8);
  printf("#define SCNoFAST16 \"%s\"\n", SCNoFAST16);
  printf("#define SCNoFAST32 \"%s\"\n", SCNoFAST32);
  printf("#define SCNoFAST64 \"%s\"\n", SCNoFAST64);

  printf("#define SCNoMAX \"%s\"\n", SCNoMAX);

  printf("#define SCNoPTR \"%s\"\n", SCNoPTR);

  printf("#define SCNu8 \"%s\"\n", SCNu8);
  printf("#define SCNu16 \"%s\"\n", SCNu16);
  printf("#define SCNu32 \"%s\"\n", SCNu32);
  printf("#define SCNu64 \"%s\"\n", SCNu64);

  printf("#define SCNuLEAST8 \"%s\"\n", SCNuLEAST8);
  printf("#define SCNuLEAST16 \"%s\"\n", SCNuLEAST16);
  printf("#define SCNuLEAST32 \"%s\"\n", SCNuLEAST32);
  printf("#define SCNuLEAST64 \"%s\"\n", SCNuLEAST64);

  printf("#define SCNuFAST8 \"%s\"\n", SCNuFAST8);
  printf("#define SCNuFAST16 \"%s\"\n", SCNuFAST16);
  printf("#define SCNuFAST32 \"%s\"\n", SCNuFAST32);
  printf("#define SCNuFAST64 \"%s\"\n", SCNuFAST64);

  printf("#define SCNuMAX \"%s\"\n", SCNuMAX);

  printf("#define SCNuPTR \"%s\"\n", SCNuPTR);

  printf("#define SCNx8 \"%s\"\n", SCNx8);
  printf("#define SCNx16 \"%s\"\n", SCNx16);
  printf("#define SCNx32 \"%s\"\n", SCNx32);
  printf("#define SCNx64 \"%s\"\n", SCNx64);

  printf("#define SCNxLEAST8 \"%s\"\n", SCNxLEAST8);
  printf("#define SCNxLEAST16 \"%s\"\n", SCNxLEAST16);
  printf("#define SCNxLEAST32 \"%s\"\n", SCNxLEAST32);
  printf("#define SCNxLEAST64 \"%s\"\n", SCNxLEAST64);

  printf("#define SCNxFAST8 \"%s\"\n", SCNxFAST8);
  printf("#define SCNxFAST16 \"%s\"\n", SCNxFAST16);
  printf("#define SCNxFAST32 \"%s\"\n", SCNxFAST32);
  printf("#define SCNxFAST64 \"%s\"\n", SCNxFAST64);

  printf("#define SCNxMAX \"%s\"\n", SCNxMAX);

  printf("#define SCNxPTR \"%s\"\n", SCNxPTR);
  
  printf("intmax_t imaxabs(intmax_t j);\n"
         "imaxdiv_t imaxdiv(intmax_t numer, intmax_t denom);\n"
         "intmax_t strtoimax(const char * restrict nptr, char ** restrict endptr, int base);\n"
         "uintmax_t strtoumax(const char * restrict nptr, char ** restrict endptr, int base);\n"
         "intmax_t wcstoimax(const wchar_t * restrict nptr, wchar_t ** restrict endptr, int base);\n"
         "uintmax_t wcstoumax(const wchar_t * restrict nptr, wchar_t ** restrict endptr, int base);\n");
  
  return 0;
}
