-- All possible Tournament Status
abstract sig TournamentStatus {}
one sig SUBSCRIPTION_TOURNAMENT extends TournamentStatus {}
one sig ACTIVE_TOURNAMENT extends TournamentStatus {}
one sig NON_ENDABLE extends TournamentStatus {}
one sig ENDED_TOURNAMENT extends TournamentStatus {}

-- All possible Battle Status
abstract sig BattleStatus {}
one sig SUBSCRIPTION_BATTLE extends BattleStatus {}
one sig ACTIVE_BATTLE extends BattleStatus {}
one sig CONSOLIDATION_STAGE extends BattleStatus {}
one sig ENDED_BATTLE extends BattleStatus {}

-- All possible Badge Status
abstract sig BadgeStatus {}
one sig CREATED extends BadgeStatus {}
one sig ASSIGNED extends BadgeStatus {}
one sig BADGE_INVALID extends BadgeStatus {}

--Boolean definition
abstract sig Bool {}
one sig True, False extends Bool {}

--Simplified Account view: only Username and Password
sig Username {}
sig Password {}

abstract sig Account {
	username : one Username,
	password : one Password
}

sig Educator extends Account {
	createdTournaments : set Tournament
}
sig Student extends Account {}

sig Tournament {
	status : one TournamentStatus,
	battles : set Battle,
	educators : some Educator,
	participants : set Student,
	creation_date : one Int,
	registration_deadline : one Int,
	badges : set Badge
} { registration_deadline > creation_date and creation_date >= 0 }

sig Battle {
	status : one BattleStatus,
	creation_date : one Int,
	registration_deadline : one Int,
	submission_deadline : one Int,
	creator : one Educator,
	participants : set Team,
	min_team_dim : one Int,
	max_team_dim : one Int,
	needs_manual_eval : one Bool,
	manual_eval_inserted : one Bool
} { registration_deadline > creation_date and
	submission_deadline > registration_deadline and
	max_team_dim >= min_team_dim and
	min_team_dim > 0 and
	creation_date >= 0
}

sig Badge {
	status : one BadgeStatus,
	creator : one Educator,
	owner : lone Student,
	creation_date : one Int
} { creation_date >= 0 }

sig Team{
	members : some Student,
	subscription_date : one Int
} { subscription_date >= 0 }

-- Used to model current time
sig currTime {
	time : one Int
} { time > 0 }

-- FACTS

-- Account:

-- No duplicate Usernames
fact {no disj a1, a2 : Account | a1.username = a2.username }

-- All Passwords belong to an Account
fact {all p : Password | one a : Account | a.password = p }

-- Tournament:

-- No two tournaments are equal
fact { no disj t1, t2 : Tournament | t1 = t2 }

-- All battles of one tournament has the creator that is one educator in that tournament
fact { all b : Battle | all t : Tournament | b in t.battles implies
	( one e : Educator | e = b.creator and ( e in t.educators )) }

-- If there is at least one battle not ended the tournament can't be closed
fact { all t : Tournament | ( t.status = NON_ENDABLE ) iff ( one b : Battle | b in t.battles and
	b.status != ENDED_BATTLE ) }

-- One tournament has subscriptions open if and only if the deadline for subscriptions has not been reached yet
fact { all t : Tournament | t.status = SUBSCRIPTION_TOURNAMENT iff
	t.registration_deadline > currTime.time }

-- If a tournament has been closed, it will be always closed
fact { all t : Tournament | always( t.status = ENDED_TOURNAMENT implies
	after always t.status = ENDED_TOURNAMENT ) }

-- During the subscription phase a tournament can't have battles
fact { all t : Tournament | t.status = SUBSCRIPTION_TOURNAMENT implies
	# t.battles = 0  } 

-- If and only if a tournament is active or ended it has no battle that are not ended
fact { all t : Tournament | ( t.status = ACTIVE_TOURNAMENT or t.status = ENDED_TOURNAMENT ) iff
	no b : Battle | b in t.battles and b.status != ENDED_BATTLE }

-- For all tournaments exists only one creator
fact { all t : Tournament | one e : Educator | e in t.educators and t in e.createdTournaments }

-- All the battles in a tournament are created after the tournament creation
fact  { all t : Tournament | all b : Battle | b in t.battles implies
	b.creation_date >= t.creation_date }

-- There are no tournaments created by two or more educators
fact { no disj e1, e2 : Educator | all t : Tournament | e1 != e2 and
	t in e1.createdTournaments and t in e2.createdTournaments }

-- A battle can be part only of one tournament
fact { no disj t1, t2 : Tournament | all b : Battle | t1 != t2 and
	b in t1.battles and b in t2.battles }

-- A tournament will be closed if after the registration deadline there are no students registrated
fact { all t : Tournament | currTime.time >= t.registration_deadline and
	# t.participants = 0 implies t.status = ENDED_TOURNAMENT }

-- Battle:

-- No two battles are equal
fact { no disj b1, b2 : Battle | b1 = b2 }

-- All battles belong to a tournament
fact { all b : Battle | one t : Tournament | b in t.battles }

-- One battle has subscriptions open if and only if the deadline for subscriptions has not been reached yet
fact { all b : Battle | b.status = SUBSCRIPTION_BATTLE iff
	b.registration_deadline > currTime.time }

-- A team can't register in a battle after the subscription phase
fact { all b : Battle | all t : Team | t in b.participants implies
	t.subscription_date < b.registration_deadline }

-- One battle is active if and only if the deadline for submissions has not been reached yet
fact { all b : Battle | b.status = ACTIVE_BATTLE iff
	b.submission_deadline > currTime.time and currTime.time >= b.registration_deadline }

-- One battle is in consolidation phase if and only if the deadline for submissions has been reached and it needs the manual evaluation
fact { all b : Battle | b.status = CONSOLIDATION_STAGE iff
	b.submission_deadline <= currTime.time and b.needs_manual_eval = True }

-- One battle is ended if and only if the deadline for submissions has been reached and it doesn't need the manual evaluation or
--	the manual evaluation is inserted
fact { all b : Battle | b.status = ENDED_BATTLE iff
	b.submission_deadline <= currTime.time and ( b.needs_manual_eval = False or
	( b.needs_manual_eval = True and b.manual_eval_inserted = True )) }

-- If a battle has ended, it will be always ended
fact { all b : Battle | always( b.status = ENDED_BATTLE implies
	after always b.status = ENDED_BATTLE ) }

-- All the teams in a battle satisfy the members count constraints
fact { all b : Battle | all t : Team | t in b.participants implies
	( # t.members >= b.min_team_dim ) and ( # t.members =< b.max_team_dim ) }

-- If in a battle there are no registered teams, it will be closed automatically
fact { all b : Battle | ( b.registration_deadline <= currTime.time and # b.participants = 0 ) implies
	b.status = ENDED_BATTLE }

-- If a battle don't need a manual evaluation, a manual evaluation can not be inserted
fact { all b : Battle | b.needs_manual_eval = False implies 
	b.manual_eval_inserted = False}

-- There are no battles created before the tournament subscription phase
fact { all t : Tournament | no b : Battle | b in t.battles and b.creation_date <= t.registration_deadline }

-- Badge:

-- No two badges are equal
fact { no disj b1, b2 : Badge | b1 = b2 }

-- All badges belong to a tournament
fact { all b : Badge | one t : Tournament | b in t.badges }

-- A badge can be created only by the educator that has created the tournament
fact { all e : Educator | all t : Tournament | all b : Badge | ( t in e.createdTournaments and
	b in t.badges ) iff e = b.creator }

-- A badge can be created only when a tournament is created
fact { all b : Badge | all t : Tournament | b in t.badges implies
	b.creation_date = t.creation_date }

-- If and only if a badge is not already linked to a student, it's CREATED
fact { all b : Badge | # b.owner = 0 iff
	( b.status = CREATED or b.status = BADGE_INVALID ) }

-- A badge is assigned if and only if there is a student of the closed tournament that has been linked to the badge
fact { all b : Badge | all t : Tournament | b.status = ASSIGNED iff
	( b in t.badges and t.status = ENDED_TOURNAMENT and  # b.owner = 1 and b.owner in t.participants ) }

-- If and only if the tournament is closed and there are no battles in it, the badge is invalid
fact { all b : Badge | all t : Tournament | ( b in t.badges and
	t.status = ENDED_TOURNAMENT and # t.battles = 0 ) iff
	b.status = BADGE_INVALID }

-- If the badge is assigned it will always be that
fact { all b : Badge | always( b.status = ASSIGNED implies
	after always b.status = ASSIGNED ) }

-- If the badge is invalid it will always be that
fact { all b : Badge | always( b.status = BADGE_INVALID implies
	after always b.status = BADGE_INVALID ) }

-- If a badge is invalid it can't have an owner
fact { all b : Badge | no s : Student | b.status = BADGE_INVALID and s = b.owner }

-- If a tournament is closed and has at least one battle all the badges are valid and must be assigned to a student in the tournament
fact { all t : Tournament | ( t.status = ENDED_TOURNAMENT and # t.battles > 0 ) implies
	( all b : Badge | one s : Student | b in t.badges and b.status = ASSIGNED and s = b.owner and s in t.participants ) }

-- Team:

-- No two teams are equal
fact { no disj t1, t2 : Team | t1 = t2 }

-- All the teams are registered at least in one battle
fact { all t : Team | one b : Battle | t in b.participants }

-- All the teams are made up by only students that are registered in the tournament of that battle
fact { all t : Tournament | all b : Battle | all team : Team | all s : Student |
	b in t.battles and team in b.participants and s in team.members implies
	s in t.participants }

-- If a student is in a team for a battle, it can't be also a member of another team in the same battle
fact { all b : Battle | all s : Student | no disj t1, t2 : Team | t1 != t2 and (t1 in b.participants and t2 in b.participants ) and
	( s in t1.members and s in t2.members ) }

-- A team can be registered in a battle only after the battle creation and before the deadline
fact { all b : Battle | all t : Team | t in b.participants implies
	( t.subscription_date > b.creation_date and t.subscription_date < b.registration_deadline ) }

-- ASSERTIONS

-- Check that every active battle are in a not closed tournament and they are created by an educator that can manage that tournament and that
--	all the teams in that battle are formed by students registered in the tournament
assert activeBattle {
	all b : Battle | ( b.status = ACTIVE_BATTLE implies (( one t : Tournament | b in t.battles and t.status = NON_ENDABLE and
	( one e : Educator | e = b.creator and e in t.educators ) and ( some team : Team | team in b.participants and
	( all s : team.members | s in t.participants )))))
}
check activeBattle

-- Check that all the closed tournament are those with no registrations at the end of the subscription time and those without active battle
assert closeTournament {
	all t : Tournament | ( t.status = ENDED_TOURNAMENT implies (( currTime.time >= t.registration_deadline and
	# t.participants = 0 ) or ( no b : Battle | b in t.battles and b.status != ENDED_BATTLE )))
}
check closeTournament

-- Check that in every closed tournament all the badges are invalid or all the badges are assigned at one student
assert assignedBadges {
	all t : Tournament | ( t.status = ENDED_TOURNAMENT  implies
	(( all b : t.badges | b.status = BADGE_INVALID ) or
	( all b : t.badges | one s : t.participants | b.status = ASSIGNED and s = b.owner )))
}
check assignedBadges

-- Check that if a tournament is not endable is because there are active battles or battles that are waiting for a manual evaluation
--	or battle that are in subscription phase
assert nonClosableTournaments {
	all t : Tournament | ( t.status = NON_ENDABLE implies 
	( some b : Battle | b.status = ACTIVE_BATTLE or ( b.needs_manual_eval = True and b.manual_eval_inserted = False ) or
	b.status = SUBSCRIPTION_BATTLE ))
}
check nonClosableTournaments

-- Check that if a badge has not an owner is because the badge is invalid or because it's a badge of a tournament that is not already closed
assert notAssignedBadges {
	all b : Badge | ( # b.owner = 0 implies 
	(( b.status = BADGE_INVALID ) or ( one t : Tournament | t.status != ENDED_TOURNAMENT and b in t.badges )))
}
check notAssignedBadges

-- PREDICATES

-- Generate a World to show the system's Tournament
pred tournamentWorld {
	# Tournament = 1
	# Battle = 2
	# Badge = 3
	# Team = 1
	# Student = 1
	# Educator = 1
	all t : Tournament | t.status = NON_ENDABLE
}
run tournamentWorld

-- Generate a World to show the system's Battle
pred battleWorld {
	# Tournament = 1
	# Battle = 3
	# Badge = 0
	# Team = 3
}
run battleWorld

-- Generate a World to show the system's Educator
pred educatorWorld {
	# Battle = 0
	# Badge = 0
	# Educator = 3
	one t : Tournament | all e : Educator | e in t.educators
}
run educatorWorld

-- Generate a World to show the system's Student
pred studentWorld {
	# Student = 3
	# Battle = 1
	# Team = 2
	one t : Tournament | all s : Student | s in t.participants
	all s : Student | one t : Team | s in t.members
}
run studentWorld for 4

-- Generate a complete Worlds
pred completeWorld {
	# Tournament = 1
	# Battle = 3
	# Badge = 3
	# Student = 3
	# Educator = 3
	# Team = 2
	all s : Student | one t : Team | s in t.members
}
run completeWorld for 6





