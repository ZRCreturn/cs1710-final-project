#lang forge


/*********************************************************
*The abstract foundational components of game generation.*
*                        Section 1                       *
**********************************************************/

-- Two Players Total

sig Minion{
    mAttack    : one Int,              
    mHealth    : one Int,             
    mAction    : one Action,            
    mState     : one MinionState,
    mSheild    : one SheildState,
    mTaunt     : one Boolean,
    mLifesteal : one Boolean
}

abstract sig Action{}
one sig ActionCompleted, NotAction extends Action{}

abstract sig MinionState{}
one sig MinionLive, MinionDead extends MinionState{}

abstract sig SheildState{}
one sig SheildActive, SheildBroken  extends SheildState{}

abstract sig Boolean{}
one sig True, False extends Boolean{}

sig GameTime {
    turn : one Player,
    end  : one Boolean,
    tmHealth : func Minion -> Int ,
    tmAction : func Minion -> Action ,
    tmState : func Minion -> MinionState,
    tmSheild : func Minion -> SheildState
}

one sig Game {
    firstState: one GameTime,
    next: pfunc GameTime -> GameTime
}
sig Player{
    hero: one Hero,
    minions: set Minion,
    pState: one PlayerState
}
-- We assume the Red player always go first 
one sig Red, Blue extends Player{}

-- Player State Dead/Live
abstract sig PlayerState{}
one sig PlayerDead, PlayerLive extends PlayerState{}

-- 6 Heros with dimplieserent buffs for Player to pick
-- Dimplieserent Heros adding buffs to all minions of the player
sig Hero{
    hHealth  : one Int
}
// one sig Nightmare, Immortal, Paladin, Lava, Panda, Drunkard extends Hero{}
one sig Nightmare extends Hero{}
-- A total of 10 minions for the player to choose from
    -- Explanation：
        -- Each minion has attack damage, defense anti-damage, health status, 
        -- and Action (indicating whether the minion have attacked the opponent this round)
        -- minion should not attact opponent over 1 times in one round


one sig S1, S2, S3, S4, S5, S6, S7, S8 extends Minion{}
// one sig S1, S2, S3, S4 extends Minion{}




/*********************************************************
*                  State predicates checks               *
*                        Section 2                       *
**********************************************************/


-- In this component, we test the initial state.
pred NoSharedMinions {
    #{Red.minions & Blue.minions} = 0
}
pred InitPlayerStateSAT{
    all p : Player | {
        (p = Red or p = Blue)
        (p.hero = Nightmare)
        (p.pState = PlayerLive)
        (#{p.minions} = 4)
    }
    NoSharedMinions
}

-- Initialize Heros state, Set unique values to each hero's attack, defense, and health
// pred InitHeroStateSAT{
//     all h : Hero{
//         -- Nightmare
//         (h = Nightmare implies {
//             h.attack = 
//             h.defense = 
//             h.health = 
//         })
//         -- Immortal
//         (h = Immortal implies {
//             h.attack = 
//             h.defense = 
//             h.health = 
//         })
//         -- Paladin
//         (h = Paladin implies {
//             h.attack = 
//             h.defense = 
//             h.health = 
//         })
//         -- Lava
//         (h = Lava implies {
//             h.attack = 
//             h.defense = 
//             h.health = 
//         })
//         -- Panda
//         (h = Panda implies {
//             h.attack = 
//             h.defense = 
//             h.health = 
//         })
//         -- Drunkard
//         (h = Drunkard implies {
//             h.attack = 
//             h.defense = 
//             h.health = 
//         })
//     }
// }
-- Initialize all Minion state
pred InitMinionState{
    S1.mAttack = 7
    S1.mHealth = 7
    S1.mAction = NotAction
    S1.mState = MinionLive
    S1.mSheild = SheildActive
    S1.mTaunt = False

    S2.mAttack = 2
    S2.mHealth = 3
    S2.mAction = NotAction
    S2.mState = MinionLive
    S2.mSheild = SheildActive
    S2.mTaunt = False

    S3.mAttack = 4
    S3.mHealth = 5
    S3.mAction = NotAction
    S3.mState = MinionLive
    S3.mSheild = SheildBroken
    S3.mTaunt = True

    S4.mAttack = 6
    S4.mHealth = 7
    S4.mAction = NotAction
    S4.mState = MinionLive
    S4.mSheild = SheildBroken
    S4.mTaunt = True

    S5.mAttack = 5
    S5.mHealth = 5
    S5.mAction = NotAction
    S5.mState = MinionLive
    S5.mSheild = SheildBroken
    S5.mTaunt = False

    S6.mAttack = 2
    S6.mHealth = 7
    S6.mAction = NotAction
    S6.mState = MinionLive
    S6.mSheild = SheildBroken
    S6.mTaunt = False

    S7.mAttack = 4
    S7.mHealth = 7
    S7.mAction = NotAction
    S7.mState = MinionLive
    S7.mSheild = SheildBroken
    S7.mTaunt = True

    S8.mAttack = 7
    S8.mHealth = 6
    S8.mAction = NotAction
    S8.mState = MinionLive
    S8.mSheild = SheildBroken
    S8.mTaunt = False
}
pred InitGameTime{
    all m : Minion | {
        Game.firstState.turn = Blue
        Game.firstState.tmHealth[m] = m.mHealth
        Game.firstState.tmAction[m] = m.mAction
        Game.firstState.tmState[m] = m.mState
        Game.firstState.tmSheild[m] = m.mSheild
    }
}
pred InitStateChecksSAT{
    InitPlayerStateSAT
    //InitHeroStateSAT
    InitMinionState
    InitGameTime
}


// -- In this component, We test the safety of actions.
//     -- In other word, Am I able to take action safely? Action Guard
// pred stayStill[p:Player]{} -- no changes if it is my attack round
// pred playerAttackEnable[p : Player]{}
// pred minionAttackEnable[p : Player, s: Minion]{}


// -- In this component, we test for the correctness of operations (hit or defen)
// pred attackCorrectness[]{}
// pred defenseCorrectness[]{}
// pred healthCalculationCorrectness[]{}
// pred CorrectnessLiveOrDeadState[]{}



// -- procedures 

// pred GamingProcedure{
//     -- Core rule of running game
// }

// -- Trace, run the game  -- since the max teace = 14, we can not set too much health to Minions
// -- Please pay attention to the ratio of (attack: defence : Health : trace_length)

pred winningAfter [t: GameTime] {
    (all m : Blue.minions | {
        t.tmHealth[m] <= 0
    })
    or 
    (all m : Red.minions | {
        t.tmHealth[m] <= 0
    })
    
}
pred doNothing[attacker: Minion, t1, t2 : GameTime]{
    t2.tmAction[attacker] = ActionCompleted
}
pred attack[attacker, victim : Minion, t1, t2 : GameTime]{
    // attacker attack
    ((t1.tmSheild[victim] = SheildActive) =>
    (t2.tmSheild[victim] = SheildBroken and t2.tmHealth[victim] = t1.tmHealth[victim]) else 
    (t2.tmHealth[victim] = subtract[t1.tmHealth[victim], attacker.mAttack]))

    // attacker will also Paying the price of an attack -- get hurt by the victim's attack
    ((t1.tmSheild[attacker] = SheildActive)=>(
        t2.tmSheild[attacker] = SheildBroken and t2.tmHealth[attacker] = t1.tmHealth[attacker]
    ) 
    else (
        (attacker.mLifesteal = True) => (
            t2.tmHealth[attacker] = add [subtract[t1.tmHealth[attacker], victim.mAttack], attacker.mAttack]
        )
        else (
            t2.tmHealth[attacker] = subtract[t1.tmHealth[attacker], victim.mAttack]
        )
    ))
    
    // attacker will gain health if has lifesteal
    

    // state change
    (t2.tmHealth[attacker] <= 0) => (t2.tmState[attacker] = MinionDead) else (t2.tmState[attacker] = MinionLive)
    (t2.tmHealth[victim] <= 0) => (t2.tmState[victim] = MinionDead) else (t2.tmState[victim] = MinionLive)
    
    // Action state change 
    t2.tmAction[attacker] = ActionCompleted
}

pred attackFrame[attacker, victim : Minion, t1, t2 : GameTime]{
    // check victim and attacker (guard) 
    t1.tmState[attacker] = MinionLive
    t1.tmState[victim] = MinionLive
    t1.tmAction[attacker] = NotAction

    //attack(action)
    attack[attacker, victim , t1, t2]
    
    // (frame)
    
    t1.turn = t2.turn
    //whenever attack, the sheild must broken
    t2.tmSheild[attacker] = SheildBroken
    t2.tmSheild[victim] = SheildBroken
    all m3 : (Minion - attacker - victim) | {
        t1.tmHealth[m3] = t2.tmHealth[m3]
        t1.tmState[m3] = t2.tmState[m3]
        t1.tmSheild[m3] = t2.tmSheild[m3]
    }
    all m4 : (Minion - attacker) | {
        t1.tmAction[m4] = t2.tmAction[m4]
    }
}

// sig GameTime {
//     turn : one Player
//     tmHealth : func Minion -> Int 
//     tmHit : func Minion -> Hit 
//     tmState : func Minion -> MinionState
// }



pred turnChange[t1, t2 : GameTime]{
    t1.turn = Blue => t2.turn = Red else t2.turn = Blue
    // action_state change 
    all m : Minion | {
        t2.tmAction[m] = NotAction
        // guard for other fields 
        t2.tmState[m] = t1.tmState[m]
        t2.tmHealth[m] = t1.tmHealth[m]
    }
}

pred minionAction[t1, t2 : GameTime]{
    t1.turn = Blue => {
        one m1 : Blue.minions | {
            // attack
            // must attack minion with taunt first 
            (#{m : Red.minions | (m.mTaunt = True) and (t1.tmState[m] = MinionLive)} != 0) =>
            (one m2 : Red.minions | {
                m2.mTaunt = True
                attackFrame[m1,m2,t1,t2]
            }) 
            else 
            (one m2 : Red.minions | {
                attackFrame[m1,m2,t1,t2]
            }) 

            // or(
            // // or not attack 

            // // check attacker
            //     (t1.tmAction[m1] = NotAction)
            //     and
            //     // do nothing
            //     (doNothing[m1, t1, t2])
            //     and
            //     // frame 
            //     (t1.turn = t2.turn)
            //     and
            //     (all m6 : Minion | {
            //         t1.tmHealth[m6] = t2.tmHealth[m6]
            //         t1.tmState[m6] = t2.tmState[m6]
            //     })
            //     and 
            //     (all m7 : (Minion - m1) | {
            //         t1.tmAction[m7] = t2.tmAction[m7]
            //     })
            // )
        }
    }
    else {
        one m1 : Red.minions | {
            // attack
            // must attack minion with taunt first 
            (#{m : Blue.minions | (m.mTaunt = True) and (t1.tmState[m] = MinionLive)} != 0) =>
            (one m2 : Blue.minions | {
                m2.mTaunt = True
                attackFrame[m1,m2,t1,t2]
            }) 
            else 
            (one m2 : Blue.minions | {
                attackFrame[m1,m2,t1,t2]
            }) 

            // or(
            // // or not attack 

            // // check attacker
            //     (t1.tmAction[m1] = NotAction)
            //     and
            //     // do nothing
            //     (doNothing[m1, t1, t2])
            //     and
            //     // frame 
            //     (t1.turn = t2.turn)
            //     and
            //     (all m6 : Minion | {
            //         t1.tmHealth[m6] = t2.tmHealth[m6]
            //         t1.tmState[m6] = t2.tmState[m6]
            //     })
            //     and 
            //     (all m7 : (Minion - m1) | {
            //         t1.tmAction[m7] = t2.tmAction[m7]
            //     })
            // )
        }
    }
}
pred step[t1, t2 : GameTime]{
    winningAfter[t1] => 
    (all m : Minion | {
        t1.tmAction[m] = t2.tmAction[m]
        t1.tmHealth[m] = t2.tmHealth[m]
        t1.tmState[m] = t2.tmState[m]
        t1.tmSheild[m] = t2.tmSheild[m]
        t1.turn = t2.turn
        t1.end = True
        t2.end = True
    }) 
    else(
        (t1.end = False)
        and 
        (#{m : Minion | {t1.tmAction[m] = ActionCompleted}} = 4
        => (turnChange[t1, t2])
        else (minionAction[t1, t2]))
    )

}

pred traces {
    InitStateChecksSAT
    no prev : GameTime | Game.next[prev] = Game.firstState -- first state doesn't have a predecessor
    all t: GameTime |
        some Game.next[t] implies
            step [t, Game.next[t]]
}

run{
    traces
} for exactly 5 Int, 20 GameTime for {next is linear}

