/*@ function (i32) INACTIVE () { 0i32 } @*/
static int c_INACTIVE() { return 0; }
/*@ function (i32) ACTIVE () { 1i32 } @*/
static int c_ACTIVE() { return 1; }

struct State {
    int ModeA;
    int ModeD;
    int W_A;
    int W_D;
    int Runway_Time;
    int Plane_Counter;
};
/*@
function (boolean) valid_state (struct State s) {
     (s.ModeA == INACTIVE() || s.ModeA == ACTIVE()) &&
     (s.ModeD == INACTIVE() || s.ModeD == ACTIVE()) &&
     (s.ModeA == INACTIVE() || s.ModeD == INACTIVE()) &&

     (s.W_A >= 0i32 && s.W_D >= 0i32) &&
     (0i32 <= s.Runway_Time && s.Runway_Time <= 5i32) &&
     (0i32 <= s.Plane_Counter && s.Plane_Counter <= 3i32) &&

     (s.ModeA == INACTIVE() && s.ModeD == INACTIVE()
        implies s.Plane_Counter == 0i32) &&
     (s.Runway_Time > 0i32
        implies (s.ModeA == ACTIVE() || s.ModeD == ACTIVE())) &&

     (s.Plane_Counter > 0i32 && s.ModeA == ACTIVE() implies s.W_D > 0i32) &&
     (s.Plane_Counter > 0i32 && s.ModeD == ACTIVE() implies s.W_A > 0i32)
}
@*/
struct State init()
    /*@ requires true;
        ensures valid_state(return);
    @*/
{
    struct State initial = { 0,0,0,0,0,0 };
    return initial;
}
struct State increment_Plane_Counter(struct State s)
    /*@ requires valid_state(s);
                 0i32 <= s.Plane_Counter;
                 s.Plane_Counter <= 2i32;
                 s.ModeA == ACTIVE() || s.ModeD == ACTIVE();
                 s.ModeA == ACTIVE() implies s.W_D > 0i32;
                 s.ModeD == ACTIVE() implies s.W_A > 0i32;
        ensures  valid_state(return);
                 s.Plane_Counter == return.Plane_Counter - 1i32;
                 s.Runway_Time == return.Runway_Time;
                 s.ModeA == return.ModeA;
                 s.ModeD == return.ModeD;
                 s.W_A == return.W_A;
                 s.W_D == return.W_D;
    @*/
{
    struct State temp = s;
    temp.Plane_Counter = s.Plane_Counter + 1;
    return temp;
}
struct State reset_Plane_Counter(struct State s)
    /*@ requires valid_state(s);
        ensures  valid_state(return);
                 return.Plane_Counter == 0i32;
                 s.Runway_Time == return.Runway_Time;
                 s.ModeA == return.ModeA;
                 s.ModeD == return.ModeD;
                 s.W_A == return.W_A;
                 s.W_D == return.W_D;
    @*/
{
    struct State temp = s;
    temp.Plane_Counter = 0;
    return temp;
}

struct State increment_Runway_Time(struct State s)
    /* --BEGIN-- */
    /*@ requires valid_state(s);
                 0i32 <= s.Runway_Time;
                 s.Runway_Time <= 4i32;
                 s.ModeA == ACTIVE() || s.ModeD == ACTIVE();
        ensures  valid_state(return);
                 s.Plane_Counter == return.Plane_Counter;
                 s.ModeA == return.ModeA;
                 s.ModeD == return.ModeD;
    @*/
    /* --END-- */
{
    struct State temp = s;
    temp.Runway_Time = s.Runway_Time + 1;
    return temp;
}
struct State reset_Runway_Time(struct State s)
    /* --BEGIN-- */
    /*@ requires valid_state(s);
        ensures  valid_state(return);
                 return.Runway_Time == 0i32;
                 s.ModeA == return.ModeA;
                 s.ModeD == return.ModeD;
                 s.W_A == return.W_A;
                 s.W_D == return.W_D;
                 s.Plane_Counter == return.Plane_Counter;
    @*/
    /* --END-- */
{
    struct State temp = s;
    temp.Runway_Time = 0;
    return temp;
}
struct State arrive(struct State s)
    /* --BEGIN-- */
    /*@ requires valid_state(s);
                 s.ModeA == ACTIVE() && s.W_A >= 1i32;
                 s.Plane_Counter <= 2i32;
        ensures  valid_state(return);
                 s.Runway_Time == return.Runway_Time;
                 s.ModeA == return.ModeA;
                 s.ModeD == return.ModeD;
                 s.W_D == return.W_D;
                 s.W_D == 0i32
                   implies s.Plane_Counter == return.Plane_Counter;
                 s.W_D > 0i32
                   implies s.Plane_Counter == return.Plane_Counter - 1i32;
    @*/
    /* --END-- */
{
    struct State temp = s;
    temp.W_A = s.W_A - 1;
    if (s.W_D > 0) {
        temp = increment_Plane_Counter(temp);
    }
    return temp;
}
struct State depart(struct State s)
    /* --BEGIN-- */
    /*@ requires valid_state(s);
                 s.ModeD == ACTIVE() && s.W_D >=1i32;
                 s.Plane_Counter <= 2i32;
        ensures  valid_state(return);
                  s.Runway_Time == return.Runway_Time;
                  s.ModeA == return.ModeA;
                  s.ModeD == return.ModeD;
                  s.W_A == return.W_A;
    @*/
    /* --END-- */
{
    struct State temp = s;
    temp.W_D = s.W_D - 1;
    if (s.W_A > 0) {
        temp = increment_Plane_Counter(temp);
    }
    return temp;
}
struct State switch_modes(struct State s)
    /* --BEGIN-- */
    /*@ requires valid_state(s);
                 s.ModeA == ACTIVE() || s.ModeD == ACTIVE();
                 s.Plane_Counter == 0i32;
        ensures  valid_state(return);
                 return.ModeA == ACTIVE() || return.ModeD == ACTIVE();
                 return.ModeA == s.ModeD;
                 return.ModeD == s.ModeA;
                 return.W_A == s.W_A;
                 return.W_D == s.W_D;
                 return.Runway_Time == s.Runway_Time;
                 s.Plane_Counter == return.Plane_Counter;
    @*/
    /* --END-- */
{
    struct State temp = s;
    if (s.ModeA == 0) {
        // if arrival mode is inactive, make it active
        temp.ModeA = 1;
    }
    else {
        // if arrival mode is active, make it inactive
        temp.ModeA = 0;
    }
    if (s.ModeD == 0) {
        // if departure mode is inactive, make it active
        temp.ModeD = 1;
    }
    else {
        // if departure mode is active, make it inactive
        temp.ModeD = 0;
    }
    return temp;
}
// This function represents what happens every minute at the airport. 
// One `tick` corresponds to one minute.
struct State tick(struct State s)
    /* --BEGIN-- */
    /*@ requires valid_state(s);
                 (i64) s.Plane_Counter < 2147483647i64;
                 (i64) s.W_A < 2147483647i64;
                 (i64) s.W_D < 2147483647i64;
        ensures valid_state(return);
                (s.W_A > 0i32 && s.W_D == 0i32 && s.Runway_Time == 0i32
                   implies return.ModeA == ACTIVE());
                (s.W_D > 0i32 && s.W_A == 0i32 && s.Runway_Time == 0i32
                   implies return.ModeD == ACTIVE());
    @*/
    /* --END-- */
{
    // Plane on the runway
    if (s.Runway_Time > 0)
    {
        if (s.Runway_Time == 5)
        {
            s = reset_Runway_Time(s);
        }
        else {
            s = increment_Runway_Time(s);
        }
        return s;
    }
    // Plane chosen to arrive
    else if (s.ModeA == 1 && s.W_A > 0 && s.Plane_Counter < 3) {
        s = arrive(s);
        s = increment_Runway_Time(s);
        return s;
    }
    // Plane chosen to depart
    else if (s.ModeD == 1 && s.W_D > 0 && s.Plane_Counter < 3) {
        s = depart(s);
        s = increment_Runway_Time(s);
        return s;
    }
    // Need to switch modes
    else {
        // Need to switch from arrival to departure mode
        if (s.ModeA == 1) {
            s = reset_Plane_Counter(s);
            s = switch_modes(s);
            // If there are planes waiting to depart, let one depart
            if (s.W_D > 0) {
                s = depart(s);
                s = increment_Runway_Time(s);
            }
            return s;
        }
        // Need to switch from departure to arrival mode
        else if (s.ModeD == 1) {
            s = reset_Plane_Counter(s);
            s = switch_modes(s);
            // If there are planes waiting to arrive, let one arrive
            if (s.W_A > 0) {
                s = arrive(s);
                s = increment_Runway_Time(s);
            }
            return s;
        }
        // If neither mode is active, then it must be the beginning of the day.
        else {
            if (s.W_A > 0) {
                s.ModeA = 1;
                s = arrive(s);
                s = increment_Runway_Time(s);
                return s;
            }
            else if (s.W_D > 0) {
                s.ModeD = 1;
                s = depart(s);
                s = increment_Runway_Time(s);
                return s;
            }
            else {
                // No planes are waiting, so we choose arrival mode and wait
                s.ModeA = 1;
                return s;
            }
        }
    }
}
