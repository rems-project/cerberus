/* Example - Mission Protection System Voting
 *
 * This example is drawn from the VERSE TA2 Mission Protection System (MPS),
 * which is based on the MPS developed in the HARDENS project for monitoring a
 * nuclear reactor.
 *
 * This example demonstrates a CN specification implementing requirement
 * ACTUATION_LOGIC_VOTE_TEMPERATURE, which says that 2-out-of-4 coincidence
 * logic should be used to determine if a trip signal should be generated.
 *
 * It includes a simplified implementation of the MPS C function that
 * implements this requirement.
 */

#include <stdint.h>

typedef uint8_t w1;
typedef uint8_t w2;
typedef uint8_t w8;

/*@
  function (boolean) P_Coincidence_2_4(boolean a, boolean b, boolean c, boolean d) {
    (a&&b) || ((a||b) && (c||d)) || (c&&d)
  }

  function (u8) Bool_to_u8(boolean b) {
    if(b) {
      1u8
    } else {
      0u8
    }
  }
@*/

w1 Coincidence_2_4(w8 trips[4])
/*@
  requires
    take ta = Owned<uint8_t>(array_shift<uint8_t>(trips, 0i32));
    take tb = Owned<uint8_t>(array_shift<uint8_t>(trips, 1i32));
    take tc = Owned<uint8_t>(array_shift<uint8_t>(trips, 2i32));
    take td = Owned<uint8_t>(array_shift<uint8_t>(trips, 3i32));
    let a = ta != 0u8;
    let b = tb != 0u8;
    let c = tc != 0u8;
    let d = td != 0u8;
  ensures
    take ta_out = Owned<uint8_t>(array_shift<uint8_t>(trips, 0i32));
    take tb_out = Owned<uint8_t>(array_shift<uint8_t>(trips, 1i32));
    take tc_out = Owned<uint8_t>(array_shift<uint8_t>(trips, 2i32));
    take td_out = Owned<uint8_t>(array_shift<uint8_t>(trips, 3i32));
    return == Bool_to_u8(P_Coincidence_2_4(a, b, c, d));
@*/
{
    w1 v0 = trips[0] != 0;
    w1 v1 = trips[1] != 0;
    w1 v2 = trips[2] != 0;
    w1 v3 = trips[3] != 0;
    return (v0 & v1) | ((v0 | v1) & (v2 | v3)) | (v2 & v3);
}