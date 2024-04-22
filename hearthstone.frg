#lang forge/temporal


/*********************************************************
*The abstract foundational components of game generation.*
*                        Section 1                       *
**********************************************************/

-- Two Players Total

sig Minion{
    mAttack  : one Int,              
    mHealth  : one Int,             
    mAction  : one Action,            
    mState   : one MinionState      
}

abstract sig Action{}
one sig ActionCompleted, NotAction extends Action{}

abstract sig MinionState{}
one sig MinionLive, MinionDead extends MinionState{}

sig GameTime {
    turn : one Player,
    tmHealth : func Minion -> Int ,
    tmAction : func Minion -> Action ,
    tmState : func Minion -> MinionState
}

sig Game {
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


one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10 extends Minion{}




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
        (#{p.minions} = 5)
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


    S2.mAttack = 2
    S2.mHealth = 3
    S2.mAction = NotAction
    S2.mState = MinionLive


    S3.mAttack = 4
    S3.mHealth = 5
    S3.mAction = NotAction
    S3.mState = MinionLive


    S4.mAttack = 6
    S4.mHealth = 7
    S4.mAction = NotAction
    S4.mState = MinionLive


    S5.mAttack = 5
    S5.mHealth = 5
    S5.mAction = NotAction
    S5.mState = MinionLive


    S6.mAttack = 2
    S6.mHealth = 7
    S6.mAction = NotAction
    S6.mState = MinionLive


    S7.mAttack = 4
    S7.mHealth = 7
    S7.mAction = NotAction
    S7.mState = MinionLive


    S8.mAttack = 7
    S8.mHealth = 6
    S8.mAction = NotAction
    S8.mState = MinionLive


    S9.mAttack = 6
    S9.mHealth = 5
    S9.mAction = NotAction
    S9.mState = MinionLive


    S10.mAttack = 3
    S10.mHealth = 4
    S10.mAction = NotAction
    S10.mState = MinionLive
}

pred InitStateChecksSAT{
    InitPlayerStateSAT
    //InitHeroStateSAT
    InitMinionState
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
    t2.tmHealth[victim] = t1.tmHealth[victim] - attacker.mAttack
    // attacker will also Paying the price of an attack -- get hurt by the victim's attack
    t2.tmHealth[attacker] = t1.tmHealth[attacker] - victim.mAttack
    
    // state change
    (t2.tmHealth[attacker] <= 0) => (t2.tmState[attacker] = MinionDead) else (t2.tmState[attacker] = MinionLive)
    (t2.tmHealth[victim] <= 0) => (t2.tmState[victim] = MinionDead) else (t2.tmState[victim] = MinionLive)
    
    // Action state change 
    t2.tmAction[attacker] = ActionCompleted
}


// sig GameTime {
//     turn : one Player
//     tmHealth : func Minion -> Int 
//     tmHit : func Minion -> Hit 
//     tmState : func Minion -> MinionState
// }



pred turnChange[t1, t2 : GameTime]{
    t1.turn = Blue => t2.turn = Red else t2.turn = Blue
    // todo actionstate change 
}

pred minionAction[t1, t2 : GameTime]{
    GameTime.turn = Blue => {
        one m1 : Blue.minions | {
            // attack
            (one m2 : Red.minions | {
                // check victim and attacker (guard) 
                t1.tmState[m2] = MinionLive
                t1.tmAction[m1] = NotAction

                //attack(action)
                attack[m1, m2 , t1, t2]
                
                // (frame)
                all m3 : (Minion - m1 - m2) | {
                    t1.tmHealth[m3] = t2.tmHealth[m3]
                }
                all m4 : (Minion - m1) | {
                    t1.tmAction[m4] = t2.tmAction[m4]
                }
                all m5 : (Minion - m1 - m2) | {
                    t1.tmState[m5] = t2.tmState[m5]
                }
            }) 

            or
            // or not attack 

            // check attacker
            ((t1.tmAction[m1] = NotAction)
            and
            // do nothing
            (doNothing[m1, t1, t2])
            and
            // frame 
            (all m6 : Minion | {
                t1.tmHealth[m6] = t2.tmHealth[m6]
                t1.tmAction[m6] = t2.tmAction[m6]
                t1.tmState[m6] = t2.tmState[m6]
            })
            )
        }
    }
    else {
        one m1 : Red.minions | {
            // attack
            (one m2 : Blue.minions | {
                // check victim and attacker (guard) 
                t1.tmState[m2] = MinionLive
                t1.tmAction[m1] = NotAction

                //attack(action)
                attack[m1, m2 , t1, t2]
                
                // (frame)
                all m3 : (Minion - m1 - m2) | {
                    t1.tmHealth[m3] = t2.tmHealth[m3]
                }
                all m4 : (Minion - m1) | {
                    t1.tmAction[m4] = t2.tmAction[m4]
                }
                all m5 : (Minion - m1 - m2) | {
                    t1.tmState[m5] = t2.tmState[m5]
                }
            }) 

            or
            // or not attack 

            // check attacker
            ((t1.tmAction[m1] = NotAction)
            and
            // do nothing
            (doNothing[m1, t1, t2])
            and
            // frame 
            (all m6 : Minion | {
                t1.tmHealth[m6] = t2.tmHealth[m6]
                t1.tmAction[m6] = t2.tmAction[m6]
                t1.tmState[m6] = t2.tmState[m6]
            })
            )
        }
    }
}
pred step[t1, t2 : GameTime]{
    (all m : Minion | {t1.tmAction[m] = ActionCompleted}) 
    => (turnChange[t1, t2])
    else (minionAction[t1, t2 ])
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
} for exactly 5 Int, 8 GameTime for {next is linear}

