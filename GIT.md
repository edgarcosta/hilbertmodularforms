# Gitting good in e^pi steps

# The setup

1. Create your personal account for GitHub
[https://github.com/join]([https://github.com/join)

2. Fork edgarcosta/hilbertmodularforms
 * go to https://github.com/edgarcosta/hilbertmodularforms/
 * click the fork button

3. Open a terminal on your computer, and go to a folder where you would like to store your personal copy of `hilbertmodularforms`
 For example: `cd secretprojets/`

4. Clone your repository by doing:
  ```
  git clone git@github.com:YOURUSERNAME/hilbertmodularforms.git NAMEDESIRED
  ```
  where you replace `YOURUSERNAME` and `NAMEDESIRED`.
  `NAMEDESIRED` is the name of the folder where it will store your personal copy of `hilbertmodularforms`

4. 


# The development routine

## Creating a branch which is up to date with the main repository
1. Download the latest changes of the main repository to your computer with
  `git fetch upstream master`
  2. Change the code on your directory to reflect the latest changes with `git checkout -f upstream/master`
  3. Now that you are up to date, you should create a branch which will track the new changes, with ` git checkout -b NEWBRANCHNAME`

## Saving changes
  1. Do `git status` to see what files you have edited
  2. Do `git add FILENAME` for each file you would like submit changes
  3. Commit your changes on your computer with 
  ```
  git commit
  ```
  alternatively, you can also do:
  ```
  git commit -m "fixed something really important
  ```
  4. Push your changes to the internet
  ```
  git push
  ```
  if you have never pushed this branch, then it will complain and tell you what to do

## Merging my changes with the main repository
  1. Create a PR
  2. Merge the PR, you can also ask someone to quickly look into it

## Switching between branches
  You can switch between branches by doing:
  `git checkout BRANCHNAME`

# Remarks

# Exercise


