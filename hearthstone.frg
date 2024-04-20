#lang forge

/*********************************************************
*The abstract foundational components of game generation.*
*                        Section 1                       *
**********************************************************/

-- Two Players Total
sig Game {
    firstState: one gameTime,
    next: pfunc gameTime -> gameTime
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
        -- and Hit (indicating whether the minion have attacked the opponent this round)
        -- minion should not attact opponent over 1 times in one round

sig Minion{
    attack  : one Int,              
    mHealth  : one Int,             
    hit     : one Hit,            
    mState   : one MinionState      
}
one sig S1, S2, S3, S4, S5, S6, S7, S8, S9, S10 extends Minion{}

abstract sig Hit{}
one sig AttackCompleted, NotAttacked extends Hit{}

abstract sig MinionState{}
one sig MinionLive, MinionDead extends MinionState{}


sig gameTime {
    turn : one Player
    tmHealth : func Minion -> Int 
    tmHit : func Minion -> Hit 
    tmState : func Minion -> MinionState
 }


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
pred InitMinionStateSAT{
    all s : Minion {
        ((s = S1) implies {
            s.attack = 8
            s.mHealth = 8
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S2) implies {
            s.attack = 2
            s.mHealth = 3
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S3) implies {
            s.attack = 4
            s.mHealth = 5
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S4) implies {
            s.attack = 6
            s.mHealth = 7
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S5) implies {
            s.attack = 5
            s.mHealth = 5
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S6) implies {
            s.attack = 1
            s.mHealth = 10
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S7) implies {
            s.attack = 2
            s.mHealth = 8
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S8) implies {
            s.attack = 12
            s.mHealth = 12
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S9) implies {
            s.attack = 9
            s.mHealth = 5
            s.hit = NotAttacked
            s.mState = MinionLive
        })
        ((s = S10) implies {
            s.attack = 3
            s.mHealth = 4
            s.hit = NotAttacked
            s.mState = MinionLive
        })
    }
}

pred InitStateChecksSAT{
    InitPlayerStateSAT
    //InitHeroStateSAT
    InitMinionStateSAT
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


pred traces {
    InitStateChecksSAT
    no prev : gameTime | Election.next[prev] = Election.firstState -- first state doesn't have a predecessor
    all t: gameTime |
        some Game.next[t] implies
            step [t, Election.next[t]]
}
pred step[t1, t2 : gameTime]{
    gameTime.turn = Blue => {
        all m : Blue.minions | {
            // attack
            () or
            // or not attack 
            ()
        }
    }
    else {

    }
}
run{
    traces
} for exactly 5 Int

