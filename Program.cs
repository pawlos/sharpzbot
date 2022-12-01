using System;
using System.Collections;
using System.Numerics;
using System.Linq;
using static System.Math;
using static System.Linq.Enumerable;
using static Statics;
using static System.Console;
using ShellProgressBar;
//using System.Collections.Generic;

//-------------------------------------------------------------
// TYPE ALIASES 
//-------------------------------------------------------------
using u8=System.Byte;
using u16=System.UInt16;
using u32=System.UInt32;
using f32=System.Single; 
using f64=System.Double; // lazy Rust-like abbreviations

using Selection = System.Byte;// # a bitfield representing a selection of dice to roll (1 means roll, 0 means don't)
using Choice = System.Byte; // represents EITHER chosen scorecard Slot, OR a chosen dice Selection (below)
using DieVal = System.Byte; // a single die value 0 to 6 where 0 means "unselected"
using Slot = System.Byte; 
// using GameStateID = System.Int32;

//--------------------------------------------------
// Test code 
// -------------------------------------------------

// var dv = new DieVals(1,2,3,4,5); 
// foreach (var d in dv) Console.WriteLine(d);
char[] arr = new char[] {'a', 'b', 'c'};
var output = arr.perms();
var slots = new Slots(1,2,3,10);
// var doeshave = slots.has(2); 
// var tots = Slots.useful_upper_totals(slots);
// var removed = slots.removed(2);
// var doeshavenow = removed.has(2); 
// var slots2 = new Slots(1);



Init();//blech
var state = new GameState(new DieVals(1,2,3,4,5), new Slots(2), 0, 1, false);
var app = new App(state);
Write(app.ev_cache[state.id]);

// main();

//-------------------------------------------------------------
// MAIN 
//-------------------------------------------------------------
void main() {
    print_state_choices_header();
    var game = new GameState( 
        new DieVals(), // five unrolled dice
        new Slots(ACES, TWOS, THREES, FOURS, FIVES, SIXES,
            THREE_OF_A_KIND, FOUR_OF_A_KIND, FULL_HOUSE,
            SM_STRAIGHT, LG_STRAIGHT,
            YAHTZEE, CHANCE
        ), // all slots remaining in an empty scorecard
        0, // current upper section total
        3, // rolls remaining
        false // yahtzee bonus available? 
    ); 
    var app = new App(game);
    app.build_cache();
    // # starting game state, should have expected value of 255.5896
}



//-------------------------------------------------------------
//INITIALIZERS etc 
//-------------------------------------------------------------
class Statics {

    // a single scorecard slot with values ranging from ACES to CHANCE 
    public const byte ACES = 0x1; public const byte TWOS = 0x2; public const byte THREES = 0x3; 
    public const byte FOURS = 0x4; public const byte FIVES = 0x5; public const byte SIXES = 0x6;
    public const byte SM_STRAIGHT = 0xA; public const byte LG_STRAIGHT = 0xB; public const byte YAHTZEE = 0xC; public const byte CHANCE = 0xD;
    public const byte THREE_OF_A_KIND = 0x7; public const byte FOUR_OF_A_KIND = 0x8; public const byte FULL_HOUSE = 0x9; 


    public static f32[,] OUTCOME_EVS_BUFFER;
    public static u16[,] NEWVALS_DATA_BUFFER;
    public static f32[,] EVS_TIMES_ARRANGEMENTS_BUFFER; 
    public static DieValsID[] SORTED_DIEVALS;
    public static int[] RANGE_IDX_FOR_SELECTION;
    public static IEnumerable[] SELECTION_RANGES;
    public static Outcome[] OUTCOMES ; 
    public static u16[] OUTCOME_DIEVALS_DATA;
    public static u16[] OUTCOME_MASK_DATA;
    public static f32[] OUTCOME_ARRANGEMENTS;

    public static void Init() { // TODO best way?
        OUTCOME_EVS_BUFFER = new f32[1683,Environment.ProcessorCount]; 
        NEWVALS_DATA_BUFFER = new u16[1683,Environment.ProcessorCount]; 
        EVS_TIMES_ARRANGEMENTS_BUFFER  = new f32[1683,Environment.ProcessorCount]; 
        SORTED_DIEVALS = sorted_dievals();
        RANGE_IDX_FOR_SELECTION=new int[] {1,2,3,7,4,8,11,17,5,9,12,20,14,18,23,27,6,10,13,19,15,21,24,28,16,22,25,29,26,30,31,32}; 
        SELECTION_RANGES= selection_ranges(); 
        OUTCOMES = new Outcome[1683] ; 
        OUTCOME_DIEVALS_DATA = new u16[1683] ; //these 3 arrays mirror that in OUTCOMES but are contiguous and faster to access
        OUTCOME_MASK_DATA = new u16[1683] ;
        OUTCOME_ARRANGEMENTS = new f32[1683] ;
        cache_roll_outcomes_data(); 
    }

    public static List<List<T>> powerset<T> (List<T> set) {
        int size = set.Count;
        uint setsize = (uint)Pow(2,size);//set_size of power set of a set with set_size n is (2**n -1)
        int i, j;
        var outerList = new List<List<T>>(); 
        for (i = 0; i < setsize; i++) {// Run from counter 000..0 to 111..1
            var innerList = new List<T>(); // Check each jth bit in the counter is set If set then add jth element from set 
            for (j = 0; j < size; j++) if ((i & (1 << j)) > 0) innerList.Add(set[j]);
            outerList.Add(innerList);
        }
        return outerList;
    }

    public static uint factorial(uint n) { 
        if (n<=1) return 1; 
        return n * factorial(n);
    }

    // count of arrangements that can be formed from r selections, chosen from n items, 
    // where order DOES or DOESNT matter, and WITH or WITHOUT replacement, as specified.
    public static uint n_take_r(uint n, uint r, bool order_matters=false, bool with_replacement=false) {  
        if (order_matters)  //  order matters; we're counting "permutations" 
            if (with_replacement) 
                return n^r;
            else //  no replacement
                return factorial(n) / factorial(n-r);  //  this = factorial(n) when r=n
        else //  we're counting "combinations" where order doesn't matter; there are less of these 
            if (with_replacement) 
                return factorial(n+r-1) / (factorial(r)*factorial(n-1));
            else //  no replacement
                return factorial(n) / (factorial(r)*factorial(n-r));
    }

    // this generates the ranges that correspond to the outcomes, within the set of all outcomes, indexed by a give selection 
    private static IEnumerable[] selection_ranges() {
        var sel_ranges = new IEnumerable[32];
        int s = 1;
        sel_ranges[0] = Range(0,1);
        var combos = powerset<int>(new List<int>() {0,1,2,3,4});

        int i = 0;
        foreach (var combo in combos) {
            var count = (int) n_take_r(6, (uint)combo.Count, order_matters: false, with_replacement: true);
            sel_ranges[i] = Range(s,count);// s..(s + count - 1);
            s += count;
            i++;
        } 
        return sel_ranges;
    }

    // for fast access later, this generates an array of dievals in sorted form, 
    // along with each's unique "ID" between 0-252, indexed by DieVals.data
    private static DieValsID[] sorted_dievals() { 
        var vec = new DieValsID[32767];
        vec[0] = new DieValsID(); // first one is for the special wildcard 
        u8[] one_to_six = (from x in Range(1,6) select (u8)(x)).ToArray();
        u8 i=0;
        var combos = one_to_six.combos_with_rep(5);
        foreach (var combo in combos) {
            foreach (var perm in combo.perms().Distinct()) {
                var dv_perm = new DieVals(perm[0], perm[1], perm[2], perm[3], perm[4]);
                var dv_combo = new DieVals(combo[0], combo[1], combo[2], combo[3], combo[4]);
                vec[dv_perm.data] = new DieValsID(dv_combo, i);
            }
        }
        return vec;
    }

    //enables syntax like: foreach (var (j, val) in enumerate(list)) { ... }
    public static IEnumerable<(int index, T value)> enumerate<T>(IEnumerable<T> coll) => coll.Select((i, val) => (val, i));

    private static f32 distinct_arrangements_for(DieVal[] dieval_vec) { 
        var key_counts = dieval_vec.GroupBy(x=>x).Select(g=>(g.Key, (u8)g.Count()));
        uint divisor=1;
        uint non_zero_dievals=0;
        foreach (var (key, count) in key_counts){  
            if (key != 0){  
                divisor *= factorial(count);
                non_zero_dievals += count;
            } 
        } 
        return factorial(non_zero_dievals) / divisor;
    } 

    //preps the caches of roll outcomes data for every possible 5-die selection, where '0' represents an unselected die """
    private static void cache_roll_outcomes_data() { 
        var i=0; 
        var idx_combos = powerset(Range(1,5).ToList()); 
        var one_thru_six = new u8[]{1,2,3,4,5,6};
        foreach (var idx_combo_vec in idx_combos) { 
            DieVal[] dievals_vec = new DieVal[5];
            foreach (u8[] dievals_combo_vec in one_thru_six.combos_with_rep(idx_combo_vec.Count)){
                i++;
                var mask_vec = new u8[]{0b111,0b111,0b111,0b111,0b111};
                foreach( var (j, val) in enumerate(dievals_combo_vec) ){
                    var idx = idx_combo_vec[j] ;
                    dievals_vec[idx] = (DieVal)val; 
                    mask_vec[idx]=(DieVal)0;
                } 
                var arrangement_count = distinct_arrangements_for(dievals_combo_vec);
                OUTCOME_DIEVALS_DATA[i] = (new DieVals(dievals_vec)).data;
                OUTCOME_MASK_DATA[i] = (new DieVals(mask_vec)).data;
                OUTCOME_ARRANGEMENTS[i] = arrangement_count;
                OUTCOMES[i]= new Outcome( new DieVals(dievals_vec), new DieVals(mask_vec), arrangement_count);
            } 
        } 
    } 

    // returns a range which corresponds the precomputed dice roll outcome data corresponding to the given selection
    public static IEnumerable outcomes_range_for_selection(Selection selection) {
        var one_based_idx = selection + 1; // selection bitfield is 0 to 31 but Julia indexes are from 1 to 32 // TODO: valid in C#?
        var idx = RANGE_IDX_FOR_SELECTION[one_based_idx];
        var range = SELECTION_RANGES[idx]; // for @inbounds, see https://blog.tedd.no/2020/06/01/faster-c-array-access/
        return range;
    } 

    public static void print_state_choices_header() { 
        WriteLine("choice_type,choice,dice,rolls_remaining,upper_total,yahtzee_bonus_avail,open_slots,expected_value");
    } 

    // private static String[] SLOT_CODES = new String[] {"1S","2S","3S","4S","5S","6S","3K","4K","FH","SS","LS","YZ","CH"};

    // should produce one line of output kinda like ...
    // D,01111,65411,2,31,Y,1_3_4_6_7_8_11_,119.23471
    // S,13,66641,0,11,Y,3_4_5_9_10_13_,113.45208
    public static void print_state_choice(GameState state, ChoiceEV choice_ev) { 
        var sb = new System.Text.StringBuilder("", 50);
        if (state.rolls_remaining==0){ // for slot choice 
            sb.Append('S',',');
            sb.Append(choice_ev.choice); // for dice choice 
        } else {
            sb.Append('D',',');
            var str = Convert.ToString(choice_ev.choice,2);
            sb.Append(str.Substring(str.Length-5)) ;
        }
        sb.Append(',');
        sb.Append(state.rolls_remaining); sb.Append(",");
        sb.Append(state.upper_total); sb.Append(",");
        sb.Append(state.yahtzee_bonus_avail ? 1 : 0); sb.Append(",");
        sb.Append(from s in state.open_slots select s.ToString()+'_'); sb.Append(",");
        sb.Append(choice_ev.ev);
        WriteLine(sb);
    } 

}

public static class Extensions { 

    public static IEnumerable<IEnumerable<T>> Combinations<T>(this IEnumerable<T> them, int n) {
    if (n == 0) return new[] { new T[0] } ;
    return them.SelectMany((element, i) => 
        them.Skip(i + 1).Combinations(n - 1)
        .Select(combo => (new[] { element })
        .Concat(combo)));
    }

    public static List<T[]> perms<T> (this T[] arr, int k=0, int m=-1) {
        if (m==-1) m = arr.Length-1;
        var outlist= new List<T[]>(); 
        void swap (ref T a, ref T b) { T temp = a; a = b; b = temp; } 
        void perms_until(T[] arr, ref List<T[]> list, int k, int m){
            if (k == m)  list.Add(arr.ToArray()); // ToArray makes a copy
            else 
                for (int i = k; i <= m; i++) {
                    swap (ref arr[k], ref arr[i]);
                    perms_until (arr, ref list, k+1, m);
                    swap (ref arr[k], ref arr[i]);
                }
        }
        perms_until(arr, ref outlist, k, m);
        return outlist;
    }

    // All combinations of a combo_size in given[] of size n with repetitions. 
    public static List<T[]> combos_with_rep<T>(this T[] given, int combo_len, int given_len=-1) {
        if (given_len==-1) given_len = given.Length;
        var output = new List<T[]>();
        T[] current = new T[combo_len];// Allocate memory for a given combo
        combos_until(ref output, current, given, 0, combo_len, 0, given_len - 1);
        return output;
        void combos_until(ref List<T[]> output, T[] current, T[] given, int i, int combo_len, int j_start, int j_end) {
            if (i == combo_len) {// Since index has become r, current combination is fully assembled 
                output.Add(current.ToArray());
                return;
            }
            for (int j = j_start; j <= j_end; j++) {// One by one choose all elements and recur
                current[i] = given[j];
                combos_until(ref output, current, given, i + 1, combo_len, j, j_end);
            }
        }
    }


}

//-------------------------------------------------------------
//GameState
//-------------------------------------------------------------

struct GameState {
    public u32 id; // 30 bits # with the id, 
    //we can store all of below in a sparse array using 2^(8+13+6+2+1) entries = 1_073_741_824 entries = 5.2GB when storing 40bit ResultEVs 
    public DieVals sorted_dievals;// 15 bits OR 8 bits once convereted to a DieValID (252 possibilities)
    public Slots open_slots;// 13 bits        = 8_192 possibilities
    public u8 upper_total;// = 6 bits         = 64    "
    public u8 rolls_remaining;// = 2 bits     = 4     "  
    public bool yahtzee_bonus_avail;// = 1bit = 2     "

    public GameState(DieVals sorted_dievals, Slots open_slots, u8 upper_total, u8 rolls_remaining, bool yahtzee_bonus_avail) { 
        u32 dievals_id = SORTED_DIEVALS[sorted_dievals.data].id; // this is the 8-bit encoding of self.sorted_dievals
        id= dievals_id |                 // self.id will use 30 bits total...
            ( (u32)(open_slots.data)        << 7)  | // slots.data doesn't use its rightmost bit so we only shift 7 to make room for the 8-bit dieval_id above 
            ( (u32)(upper_total)            << 21) | // make room for 13+8 bit stuff above 
            ( (u32)(rolls_remaining)        << 27) | // make room for the 13+8+6 bit stuff above
            ( (u32)(yahtzee_bonus_avail?1:0)<< 29);   // make room for the 13+8+6+2 bit stuff above
        this.sorted_dievals = sorted_dievals;
        this.open_slots = open_slots;
        this.upper_total = upper_total;
        this.rolls_remaining = rolls_remaining;
        this.yahtzee_bonus_avail = yahtzee_bonus_avail;
    } 

    // # combines all GameState field bits to form a unique GameState ID
    // Base.hash(self::GameState, h::UInt) = 
    //     hash(
    //         self.sorted_dievals.data, hash(
    //             self.open_slots.data, hash(
    //                 self.upper_total, hash(
    //                     self.rolls_remaining, hash(
    //                         self.yahtzee_bonus_avail, h
    //     )))))

    // Base.isequal(self::GameState, other::GameState) = 
    //     isequal(self.sorted_dievals.data, other.sorted_dievals.data) && 
    //     isequal(self.open_slots.data, other.open_slots.data) && 
    //     isequal(self.upper_total, other.upper_total) && 
    //     isequal(self.rolls_remaining, other.rolls_remaining) && 
    //     isequal(self.yahtzee_bonus_avail, other.yahtzee_bonus_avail) 

 
    // calculate relevant counts for gamestate: required lookups and saves
    public (int, int) counts() { 
        var lookups = 0; 
        var saves = 0; 
        var false_true = new bool[] {true, false};
        var just_false = new bool[] {false};
        foreach (var subset_len in Range(1,open_slots.Count)){
            var combos = open_slots.Combinations(subset_len);
            foreach (var slots_vec in combos ) { 
                var slots = new Slots(slots_vec.ToArray());
                var joker_rules = slots.has(YAHTZEE); // yahtzees aren't wild whenever yahtzee slot is still available 
                var totals = Slots.useful_upper_totals(slots); 
                foreach (var _ in totals) {
                    foreach (var __ in joker_rules? false_true : just_false ){
                        var slot_lookups = (subset_len * subset_len==1? 1 : 2) * 252; // * subset_len as u64;
                        var dice_lookups = 848484; // // previoiusly verified by counting up by 1s in the actual loop. however chunking forward is faster 
                        lookups += dice_lookups + slot_lookups;
                        saves+=1;
        } } } }
        return ( lookups, saves ) ;
    } 

    public u8 score_first_slot_in_context() { 

        // score slot itself w/o regard to game state 
            Slot slot = open_slots.First();
            var score = Score.slot_with_dice(slot, sorted_dievals) ;

        // add upper bonus when needed total is reached 
            if (slot<=SIXES && upper_total<63){
                var new_total = Min(upper_total+score, 63 ); 
                if (new_total==63) // we just reach bonus threshold
                    score += 35;   // add the 35 bonus points 
            } 

        // special handling of "joker rules" 
            var just_rolled_yahtzee = Score.yahtzee(sorted_dievals)==50;
            var joker_rules_in_play = (slot != YAHTZEE); // joker rules in effect when the yahtzee slot is not open 
            if (just_rolled_yahtzee && joker_rules_in_play){ // standard scoring applies against the yahtzee dice except ... 
                if (slot==FULL_HOUSE)  score=25;
                if (slot==SM_STRAIGHT) score=30;
                if (slot==LG_STRAIGHT) score=40;
            } 

        // # special handling of "extra yahtzee" bonus per rules
            if (just_rolled_yahtzee && yahtzee_bonus_avail) score+=100;

        return score;
    } 

} 


//-------------------------------------------------------------
//SCORING FNs
//-------------------------------------------------------------

struct Score {

    public static u8 upperbox(u8 boxnum, DieVals sorted_dievals) { 
        u8 sum = 0;
        foreach (var d in sorted_dievals) if (d==boxnum) sum+=boxnum ;
        return sum; 
    } 

    public static u8 n_of_a_kind(u8 n, DieVals sorted_dievals) { 
        u8 inarow=1; u8 maxinarow=1; u8 lastval=100; u8 sum=0; 
        foreach (var x in sorted_dievals) { 
            if (x==lastval && x!=0) inarow +=1; else inarow=1; 
            maxinarow = Max(inarow,maxinarow);
            lastval = x;
            sum+=x;
        } 
        if (maxinarow>=n) return sum; else return 0 ;
    } 

    public static u8 straight_len(DieVals sorted_dievals) { 
        u8 inarow=1; 
        u8 lastval=254; // stub
        u8 maxinarow=1;
        foreach (var x in sorted_dievals ){
            if (x==lastval+1 && x!=0) 
                inarow+=1;
            else if (x!=lastval) 
                inarow=1; 
            maxinarow = Max(inarow,maxinarow);
            lastval = x;
        }; 
        return maxinarow;;
    } 

    public static u8 aces(DieVals sorted_dievals)             { return upperbox(0x1,sorted_dievals);}
    public static u8 twos(DieVals sorted_dievals)             { return upperbox(0x2,sorted_dievals);} 
    public static u8 threes(DieVals sorted_dievals)           { return upperbox(0x3,sorted_dievals);} 
    public static u8 fours(DieVals sorted_dievals)            { return upperbox(0x4,sorted_dievals);} 
    public static u8 fives(DieVals sorted_dievals)            { return upperbox(0x5,sorted_dievals);} 
    public static u8 sixes(DieVals sorted_dievals)            { return upperbox(0x6,sorted_dievals);} 
        
    public static u8 three_of_a_kind(DieVals sorted_dievals)  { return n_of_a_kind(0x3,sorted_dievals);} 
    public static u8 four_of_a_kind(DieVals sorted_dievals)   { return n_of_a_kind(0x4,sorted_dievals);} 
    public static u8 sm_str8(DieVals sorted_dievals)          { return (u8)(straight_len(sorted_dievals)>4? 30 : 0);}
    public static u8 lg_str8(DieVals sorted_dievals)          { return (u8)(straight_len(sorted_dievals)==5? 40 : 0);}

    // The official rule is that a Full House is "three of one number and two of another
    public static u8 fullhouse(DieVals sorted_dievals){ 
        var valcounts1 = 0; var valcounts2 = 0;
        var j=0;
        foreach ( var (i,val) in enumerate(sorted_dievals)) { 
            if (val==0) return (u8)0 ;
            if (j==0 || sorted_dievals[i]!=sorted_dievals[i-1]) j+=1; 
            if (j==1) valcounts1+=1; 
            if (j==2) valcounts2+=1; 
            if (j==3) return 0 ;
        } 
        if (valcounts1==3 && valcounts2==2 || valcounts2==3 && valcounts1==2) return 25; 
        return 0 ;
    } 
        
    public static u8 chance(DieVals sorted_dievals) {return (u8)sorted_dievals.Sum(x=>(int)x);}
        
    public static u8 yahtzee(DieVals sorted_dievals){ 
        if (sorted_dievals[0]==0) return 0 ; 
        return (u8)(sorted_dievals[1] == sorted_dievals[5]? 50 : 0) ;
    }

    // reports the score for a set of dice in a given slot w/o regard for exogenous gamestate (bonuses, yahtzee wildcards etc) 
    public static u8 slot_with_dice(Slot slot, DieVals sorted_dievals) { 
        if (slot==ACES) return aces(sorted_dievals) ; 
        if (slot==TWOS) return twos(sorted_dievals) ; 
        if (slot==THREES) return threes(sorted_dievals) ; 
        if (slot==FOURS) return fours(sorted_dievals) ; 
        if (slot==FIVES) return fives(sorted_dievals) ; 
        if (slot==SIXES) return sixes(sorted_dievals) ; 
        if (slot==THREE_OF_A_KIND) return three_of_a_kind(sorted_dievals) ; 
        if (slot==FOUR_OF_A_KIND) return four_of_a_kind(sorted_dievals) ; 
        if (slot==SM_STRAIGHT) return sm_str8(sorted_dievals) ; 
        if (slot==LG_STRAIGHT) return lg_str8(sorted_dievals) ; 
        if (slot==FULL_HOUSE) return fullhouse(sorted_dievals) ; 
        if (slot==CHANCE) return chance(sorted_dievals) ; 
        if (slot==YAHTZEE) return yahtzee(sorted_dievals) ; 
        throw new Exception(); //shouldn't get here
    }

}

//-------------------------------------------------------------
//APP
//-------------------------------------------------------------

struct App{
    public GameState game;
    public ChoiceEV[] ev_cache;
    public ProgressBar bar;

    // return a newly initialized app
    public App(GameState game) {
        var (lookups, saves) = game.counts();
        var bar = new ProgressBar(lookups,"...",ConsoleColor.Gray); 
        var ev_cache = new ChoiceEV[2^30]; // 2^30 bits hold all unique game states
        this.game = game;
        this.ev_cache = ev_cache;
        this.bar = bar;
    } 

    static void output_state_choice(GameState state, ChoiceEV choice_ev){ 
        // Uncomment below for more verbose progress output at the expense of speed 
        // println(state, choice_ev, Threads.threadid() ) #.printed(state, choice_ev)
        // print_state_choice(state,choice_ev)
    } 

    //-------------------------------------------------------------
    //    BUILD_CACHE
    //-------------------------------------------------------------

    // gather up expected values in a multithreaded bottom-up fashion. this is like.. the main thing
    public void build_cache() {

        var all_dieval_combos =  from int i in outcomes_range_for_selection(0b11111) select OUTCOMES[i].dievals ; 
        var placeholder_dievals = new DieVals();
        var placeholder_dievals_vec = new DieVals[] {placeholder_dievals};

        var false_true = new bool[] {true, false}; // NOTE These were stack alloc(?) tuples in Julia
        var just_false = new bool[] {false};

        // first handle special case of the most leafy leaf calcs -- where there's one slot left and no rolls remaining
        foreach (var single_slot in game.open_slots){
            Slots slot = new Slots(new Slot[] {single_slot}); // set of a single slot 
            var joker_rules_in_play = (single_slot != YAHTZEE); // joker rules in effect when the yahtzee slot is not open 
            foreach (var yahtzee_bonus_available in joker_rules_in_play? false_true: just_false){ // yahtzee bonus -might- be available when joker rules are in play 
                foreach (u8 upper_total in Slots.useful_upper_totals(all_unused_slots:slot)){
                    foreach (var dieval_combo in all_dieval_combos){
                        var state = new GameState(dieval_combo, slot, upper_total, 0, yahtzee_bonus_available);
                        var score = state.score_first_slot_in_context();
                        var choice_ev = new ChoiceEV(single_slot, score);
                        ev_cache[state.id] = choice_ev;
                        output_state_choice(state, choice_ev);
        } } } } 


        // for each length 
        foreach ( var slots_len in Range(1, game.open_slots.Count()) ) {

            // for each slotset (of above length)
            foreach (var slots_vec in game.open_slots.Combinations<Slot>(slots_len) ){
                Slots slots = new Slots(slots_vec.ToArray());
                var joker_rules_in_play = !slots.has(YAHTZEE); // joker rules are in effect whenever the yahtzee slot is already filled 

                // for each upper total 
                foreach (u8 upper_total in Slots.useful_upper_totals(slots)){

                    // for each yahtzee bonus possibility 
                    foreach (var yahtzee_bonus_available in joker_rules_in_play? false_true: just_false){ // bonus always unavailable unless yahtzees are wild first

                        var ticks = 848484; //dice selection cache reads =# + (252 * slots_len * (2-(slots_len==1)) ) #= slot selection cache reads =#
                        // update!(self.bar, self.bar.counter + ticks) # advance the progress bar by the number of cache reads coming up for dice selection 

                        // # for each rolls remaining
                        foreach (u8 rolls_remaining in new u8[]{0,1,2,3}) {

                            IEnumerable dieval_combos = rolls_remaining==3? placeholder_dievals_vec : all_dieval_combos;

                            foreach (var dieval_combo in dieval_combos) { /*Threads.@threads :static*/ 
                                // process_dieval_combo!(
                                //     rolls_remaining,
                                //     slots_len,
                                //     slots,
                                //     dieval_combo,
                                //     joker_rules_in_play,
                                //     yahtzee_bonus_available,
                                //     upper_total,
                                //     placeholder_dievals
                                // );
                            } // for die_combo in die_combos

                        } // for each rolls_remaining
                    } // for each yahtzee_bonus_avail
                } // for each upper total 
            }// for each slot_vec
        }// for each length

    
    }

    void process_dieval_combo(u8 rolls_remaining, u8 slots_len, Slots slots, DieVals dieval_combo, bool joker_rules_in_play, 
                              bool yahtzee_bonus_available, u8 upper_total, DieVals placeholder_dievals) { 

        var threadid = 0; //TODO implement actual C# threading // threadid = Threads.threadid()

        if (rolls_remaining==0 && slots_len > 1) { // slot selection, but not leaf calcs already recorded

            //= HANDLE SLOT SELECTION  =//

            var slot_choice_ev=new ChoiceEV(0,0);

            foreach (var slot in slots) { 

                // joker rules say extra yahtzees must be played in their matching upper slot if it's available
                u8 first_dieval = dieval_combo[1];
                bool joker_rules_matter = joker_rules_in_play && Score.yahtzee(dieval_combo)>0 && slots.has(first_dieval);
                Slot head_slot = joker_rules_matter? first_dieval : slot;

                bool yahtzee_bonus_avail_now = yahtzee_bonus_available;
                u8 upper_total_now = upper_total;
                DieVals dievals_or_placeholder = dieval_combo;
                var head_plus_tail_ev = 0f;
                u8 rolls_remaining_now = 0;

                // find the collective ev for the all the slots with this iteration's slot being first 
                // do this by summing the ev for the first (head) slot with the ev value that we look up for the remaining (tail) slots
                var passes = slots_len==1 ? 1 : 2; // to do this, we need two passes unless there's only 1 slot left
                foreach (var i in Range(1,passes)) {
                    var slots_piece = (i==1)? new Slots(new Slot[]{head_slot}) : slots.removed(head_slot);  // work on the head only or the set of slots without the head
                    var upper_total_to_save = (upper_total_now + slots_piece.best_upper_total() >= 63)? upper_total_now : (u8)(0);  // only relevant totals are cached
                    var state_to_get = new GameState(
                        dievals_or_placeholder,
                        slots_piece, 
                        upper_total_to_save,
                        rolls_remaining_now, 
                        yahtzee_bonus_avail_now
                    );
                    var choice_ev = ev_cache[state_to_get.id];
                    if (i==1 && slots_len > 1) {// prep 2nd pass on relevant 1st pass only..  
                        // going into tail slots next, we may need to adjust the state based on the head choice
                        if (choice_ev.choice <= SIXES){  // adjust upper total for the next pass 
                            var added = (u8)(choice_ev.ev % 100); // the modulo 100 here removes any yathzee bonus from ev since that doesnt' count toward upper bonus total
                            upper_total_now = (u8) Min(63, upper_total_now + added);
                        } else if (choice_ev.choice==YAHTZEE) {  // adjust yahtzee related state for the next pass
                            if (choice_ev.ev>0f) yahtzee_bonus_avail_now=true; 
                        } 
                        rolls_remaining_now=3; // for upcoming tail lookup, we always want the ev for 3 rolls remaining
                        dievals_or_placeholder= placeholder_dievals; // for 4 rolls remaining, use "wildcard" representative dievals since dice don't matter when rolling all of them
                    }
                    head_plus_tail_ev += choice_ev.ev;
                }//for i in passes 

                if (head_plus_tail_ev >= slot_choice_ev.ev) { 
                    slot_choice_ev = new ChoiceEV(slot, head_plus_tail_ev);
                } 
                
                if (joker_rules_matter) break; // if joker-rules-matter we were forced to choose one slot, so we can skip trying the rest  

            }//for slot in slots                               

            var state_to_set = new GameState(
                dieval_combo,
                slots,
                upper_total, 
                0, 
                yahtzee_bonus_available
            ); 
            ev_cache[state_to_set.id] = slot_choice_ev;
            // output_state_choice(this, state_to_set, slot_choice_ev)

        } else if (rolls_remaining > 0) {  

        //= HANDLE DICE SELECTION =//    

            u8 next_roll = (u8)(rolls_remaining-1);
            var best = new ChoiceEV(0,0f);//  selections are bitfields where '1' means roll and '0' means don't roll 
            var selections = rolls_remaining==3? Range(0b11111,1) : Range(0b00000,32); //TODO test. hoist? //select all dice on the initial roll, else try all selections
            
            foreach (u8 selection in selections) { // we'll try each selection against this starting dice combo  
                var avg_ev_for_selection = avg_ev(dieval_combo, selection, slots, upper_total, next_roll,yahtzee_bonus_available, ev_cache, threadid); // @inline
                if (avg_ev_for_selection > best.ev){
                    best = new ChoiceEV(selection, avg_ev_for_selection);
                } 
            } 
            var state_to_set = new GameState(
                dieval_combo,
                slots, 
                upper_total, 
                rolls_remaining, 
                yahtzee_bonus_available 
            ); 
            // output_state_choice(this, state_to_set, best);
            ev_cache[state_to_set.id] = best;

        }// if rolls_remaining...  
    }// process_dieval_combo

    
    f32 avg_ev(DieVals start_dievals, Selection selection, Slots slots, u8 upper_total, 
                u8 next_roll, bool yahtzee_bonus_available, ChoiceEV[] ev_cache, int threadid) { 

        var total_ev_for_selection = 0f ;
        var outcomes_arrangements_count = 0f;
        var range = outcomes_range_for_selection(selection);
    
        foreach (int i in range) { //@inbounds @simd  
            NEWVALS_DATA_BUFFER[i, threadid] = (u16)(start_dievals.data & OUTCOME_MASK_DATA[i]);
            NEWVALS_DATA_BUFFER[i, threadid] |= OUTCOME_DIEVALS_DATA[i];
        } 

        var floor_state_id = new GameState(
            new DieVals(),
            slots, 
            upper_total, 
            next_roll, // we'll average all the 'next roll' possibilities (which we'd calclated last) to get ev for 'this roll' 
            yahtzee_bonus_available 
        ).id;

        foreach (u32 i in range ){ //@inbounds 
            //= gather sorted =#
                u32 newvals_datum = NEWVALS_DATA_BUFFER[i, threadid];
                u32 sorted_dievals_id = SORTED_DIEVALS[newvals_datum].id;
            //= gather ev =#
                u32 state_to_get_id = floor_state_id | sorted_dievals_id;
                var cache_entry = ev_cache[state_to_get_id];
                OUTCOME_EVS_BUFFER[i, threadid] = cache_entry.ev;
        } 

        foreach(int i in range) {// we looped through die "combos" but we need to average all "perumtations" // @fastmath @inbounds @simd ivdep 
            EVS_TIMES_ARRANGEMENTS_BUFFER[i, threadid] = OUTCOME_EVS_BUFFER[i, threadid] * OUTCOME_ARRANGEMENTS[i];
            total_ev_for_selection +=  EVS_TIMES_ARRANGEMENTS_BUFFER[i, threadid] ;
            outcomes_arrangements_count += OUTCOME_ARRANGEMENTS[i] ;
        } 

        return  total_ev_for_selection / outcomes_arrangements_count;

    } // avg_ev
 
}

struct DieValsID { 
    public DieValsID(DieVals dievals, u8 id){ this.dievals = dievals; this.id = id; }
    public DieVals dievals = new DieVals(); 
    public u8 id = 0;
}

//-------------------------------------------------------------
//ChoiceEV
//-------------------------------------------------------------
struct ChoiceEV {
    public Choice choice;
    public float ev;
    public ChoiceEV(Choice choice, float ev){ this.choice = choice; this.ev = ev; }
}

//#=-------------------------------------------------------------
//DieVals
//-------------------------------------------------------------=#
struct DieVals : IReadOnlyList<DieVal>{// AbstractArray{DieVal, 1} 
    public u16 data=0;// 5 dievals, each from 0 to 6, can be encoded in 2 bytes total, each taking 3 bits
    private int idx =0;
    public int Count => 5;
    // public DieVals(DieVal dievalData) { data = dievalData; idx=0;}
    public byte this[int i]  => (byte) ((this.data >> (i*3)) & 0b111);
    public DieVals(params DieVal[] dievals) { 
        for (int i = 0; i < dievals.Length; i++) { 
            this.data |= (u16) (dievals[i] << (i*3)); 
        } 
    }
    // public DieVals(DieVal d1, DieVal d2, DieVal d3, DieVal d4, DieVal d5) {
    //     data = (ushort)(d5 << 12 | d4 << 9 | d3 << 6 | d2 << 3 | d1);
    // }
    IEnumerator IEnumerable.GetEnumerator() { throw new NotImplementedException(); }
    public IEnumerator<DieVal> GetEnumerator() {
        while (idx < 5) {
            yield return this[idx];
            idx++;
        }
    }
}

//-------------------------------------------------------------
// Slots
// ------------------------------------------------------------
struct Slots : IReadOnlyList<Slot> {
    public u16 data = 0; // 13 sorted Slots can be positionally encoded in one u16
    private u16 state = 0;

    public Slots(params Slot[] args) {  
        u16 mask; 
        foreach (var slot in args) {
            mask = (u16)(0x0001 << slot);
            data |= mask; // force on
        } 
        state=data;
    }

    public Slot this[int i] {
        get {
            // @assert(i<=length(self))
            var bits = data;
            var bit_index=0;
            var j=1;
            while (j <= i){ //the slots.data does not use the rightmost (0th) bit; 
                bit_index = TrailingZeroCount(bits);
                bits = (u16)(bits & (~( 1 << bit_index) ));  //unset bit
                j++;
            } 
            return (Slot)bit_index;
        }
    }

    public int Count => (int)PopCount(data); 

    IEnumerator IEnumerable.GetEnumerator() { throw new NotImplementedException(); }
    public IEnumerator<byte> GetEnumerator() {
        while (state != 0x0000) { 
            var zero_count = TrailingZeroCount(state) ;
            var mask = ~( 0x001 << (u16)zero_count );
            state = (u16)(state & mask); // force off
            yield return (Slot)(zero_count);
        }
    }

    private static int TrailingZeroCount(uint x) => PopCount(~x & (x - 1));
    private static int PopCount(uint b) { // from https://bits.houmus.org/_posts/2018-08-18-netcoreapp3.0-intrinsics-in-real-life-pt1
        b -= (b >> 1) & 0x55555555;
        b =  (b & 0x33333333) + ((b >> 2) & 0x33333333);
        b =  (b + (b >> 4)) & 0x0f0f0f0f;
        return unchecked((int) ((b * 0x01010101) >> 24));
    }

    public bool has(Slot slot) { 
        return 0x0000 < (this.data & (0x0001<<(u16)(slot)));
    } 

    public Slots removed(Slot slot_to_remove ) { 
        var mask = ~( 1 << (u16)(slot_to_remove) );
        var newdata = (u16)(this.data & mask); //# force off
        return slotsFromData(newdata);
    } 

    private static Slots slotsFromData(u16 data){
        var slots = new Slots(); 
        slots.data = data;
        slots.state = data; 
        return slots;
    }

    private static bool iseven(Slot x){ return x%2==0; } 
    private static bool iseven(int x) { return x%2==0; } // TODO some generic way to avoid dupe ?

    // a non-exact but fast estimate of relevant_upper_totals
    // ie the unique and relevant "upper bonus total" that could have occurred from the previously used upper slots
    public static IEnumerable<int> useful_upper_totals(Slots all_unused_slots) { 
        var totals = from x in Range(0,63) select x; //(x for x in 0:63)
        var used_uppers = used_upper_slots(all_unused_slots);
        if (used_uppers.All(iseven))  {
            totals = from x in totals where iseven(x) select x;
        } 
        // filter out the lowish totals that aren't relevant because they can't reach the goal with the upper slots remaining 
        // this filters out a lot of dead state space but means the lookup function must later map extraneous deficits to a default 
        int best_unused_slot_total = best_upper_total(all_unused_slots);
        // totals = (x for x in totals if x + best_unused_slot_total >=63 || x==0)
        totals = from x in totals where (x + best_unused_slot_total >=63 || x==0) select x;
        return totals;
    }

    public u8 best_upper_total(){ 
        u8 sum=0;
        foreach (var x in this) {  
            if (6<x) break; 
            sum+=x;
        } 
        return (u8)(sum*5);
    } 

    public static Slots used_upper_slots(Slots unused_slots) {
        var all_bits_except_unused_uppers = ~unused_slots.data; // "unused" slots (as encoded in .data) are not "previously used", so blank those out
        var all_upper_slot_bits = (u16) ((1<<7)-2);  // upper slot bits are those from 2^1 through 2^6 (.data encoding doesn't use 2^0)
        var previously_used_upper_slot_bits = (u16) (all_bits_except_unused_uppers & all_upper_slot_bits);
        return slotsFromData( previously_used_upper_slot_bits );
    } 

    public static u8 best_upper_total(Slots slots){  
        u8 sum=0;
        foreach (var s in slots) { if (6<s) break; sum+=s; } 
        return (u8)(sum*5);
    } 


}

//-------------------------------------------------------------
// Outcome
//-------------------------------------------------------------
struct Outcome { 
    public DieVals dievals;// = new DieVals();
    public DieVals mask;// = new DieVals(); // stores a pre-made mask for blitting this outcome onto a GameState.DieVals.data u16 later
    public f32 arrangements;// = 0; //# how many indistinguisable ways can these dievals be arranged (ie swapping identical dievals)
    public Outcome() { 
        this.dievals = new DieVals();
        this.mask = new DieVals();
        this.arrangements = 0;
    }
    public Outcome(DieVals dievals, DieVals mask, f32 arrangements) {
        this.dievals = dievals;
        this.mask = mask;
        this.arrangements = arrangements;
    }
}
